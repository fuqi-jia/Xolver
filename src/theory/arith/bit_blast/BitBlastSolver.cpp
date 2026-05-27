#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "sat/SatSolver.h"
#include <cstdlib>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <iostream>

namespace zolver::bitblast {

uint64_t BitBlastSolver::defaultGateBudget() {
    // Max fresh SAT variables the bit-blast encoder may allocate. Both the
    // encoding AND the subsequent CaDiCaL solve consume memory; empirically a
    // 2 GB process OOMs (bad_alloc) somewhere between ~0.2M and ~0.5M vars on
    // dense high-degree QF_NIA. 200k stays safely under that, keeps the curated
    // NIA suite (tiny encodings) unaffected, and turns the AProVE blow-ups into
    // a clean Unknown. Env-tunable: competition runs with more RAM should raise
    // ZOLVER_NIA_BITBLAST_GATE_BUDGET to solve larger bounded instances.
    if (const char* e = std::getenv("ZOLVER_NIA_BITBLAST_GATE_BUDGET")) {
        char* end = nullptr;
        unsigned long long v = std::strtoull(e, &end, 10);
        if (end != e && v > 0) return static_cast<uint64_t>(v);
    }
    return 200000ull;
}

bool BitBlastSolver::applicable(const std::vector<NormalizedNiaConstraint>& cs) const {
    for (const auto& c : cs) {
        if (!kernel_.terms(c.poly)) return false;   // need monomial decomposition
    }
    return true;
}

void BitBlastSolver::encodeDomainBounds(
    BitBlastEncoder& enc,
    const std::unordered_map<std::string, BitVec>& varBits,
    const DomainStore& domains) {
    // Confine the SAT search to the DomainStore box so the search space EQUALS
    // [lb,ub]^n ∩ cs (not the raw two's-complement width range).
    for (const auto& kv : varBits) {
        const IntDomain* d = domains.getDomain(kv.first);
        if (!d) continue;
        const BitVec& x = kv.second;
        // Sign fixing (BLAN): a strictly-negative domain pins the sign bit to 1,
        // a non-negative domain pins it to 0. Redundant with the bound
        // subtractors below, but a direct unit the SAT solver sees immediately
        // (reuses the existing sign-bit literal — no new constant is minted).
        if (x.width() > 0) {
            if (d->hasUpper && d->upper.value < 0)       enc.assertLit(x.sign());
            else if (d->hasLower && d->lower.value >= 0) enc.assertLit(x.sign().negated());
        }
        if (d->hasLower) {  // x >= lb  <=>  (x - lb) >= 0
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(d->lower.value)), Relation::Geq));
        }
        if (d->hasUpper) {  // x <= ub  <=>  (x - ub) <= 0
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(d->upper.value)), Relation::Leq));
        }
        if (d->finiteValues) {  // x ∈ {v1,...}  <=>  OR_i (x == vi)
            std::vector<SatLit> disj;
            for (const auto& v : *d->finiteValues)
                disj.push_back(enc.eq(x, enc.mkConst(v)));
            if (disj.empty()) { enc.assertLit(enc.constFalse()); }   // empty set => UNSAT
            else {
                SatLit acc = disj[0];
                for (size_t i = 1; i < disj.size(); ++i) acc = enc.orGate(acc, disj[i]);
                enc.assertLit(acc);
            }
        }
        for (const auto& ex : d->excludedValues) {  // x != v
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(ex.first)), Relation::Neq));
        }
    }
}

bool BitBlastSolver::modelInDomains(const IntegerModel& model, const DomainStore& domains) {
    for (const auto& entry : domains.getAllDomains()) {
        const std::string& var = entry.first;
        const IntDomain& d = entry.second;
        auto it = model.find(var);
        if (it == model.end()) continue;            // var not encoded; nothing to check
        const mpz_class& v = it->second;
        if (d.hasLower && v < d.lower.value) return false;
        if (d.hasUpper && v > d.upper.value) return false;
        if (d.finiteValues && d.finiteValues->count(v) == 0) return false;
        if (d.excludedValues.count(v)) return false;
    }
    return true;
}

std::optional<TheoryConflict> BitBlastSolver::buildCompleteConflict(
    const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains) const {
    // The encoded conjunction (all cs constraints AND every encoded domain
    // restriction) is infeasible over the complete box, so the negation of
    // EVERY justifying reason literal is a sound theory lemma. CRITICAL: every
    // restriction we encoded must contribute its reason. If any encoded
    // restriction has NO usable reason, we cannot prove the conjunction sound —
    // silently dropping it would yield an UNSOUND conflict (e.g. "¬A ∨ ¬B" when
    // the real infeasibility also needed an unjustified bound). So we bail to
    // Unknown rather than emit a partial conflict.
    //
    // POLARITY: reasons are stored in their *asserted* (true-under-model) form,
    // matching the NIA convention (see DomainStore::buildEmptyDomainConflict).
    // TheoryManager::makeFalsifiedConflict negates them into the falsified
    // clause `⋁ ¬reason`. Negating here would double-negate and produce an
    // all-true clause the propagator rejects (UnsatComplete → silently lost).
    TheoryConflict cf;

    auto pushAll = [&](const std::vector<SatLit>& reasons) -> bool {
        if (reasons.empty()) return false;
        for (const auto& l : reasons) {
            if (l.var == 0) return false;
            cf.clause.push_back(l);
        }
        return true;
    };
    auto pushOne = [&](SatLit l) -> bool {
        if (l.var == 0) return false;
        cf.clause.push_back(l);
        return true;
    };

    for (const auto& c : cs) {
        if (!pushOne(c.reason)) return std::nullopt;
    }
    for (const auto& entry : domains.getAllDomains()) {
        const IntDomain& d = entry.second;
        if (d.hasLower && !pushAll(d.lower.reasons)) return std::nullopt;
        if (d.hasUpper && !pushAll(d.upper.reasons)) return std::nullopt;
        if (d.finiteValues && !pushAll(d.finiteSetReasons)) return std::nullopt;
        for (const auto& ex : d.excludedValues) {
            if (!pushAll(ex.second)) return std::nullopt;
        }
    }

    if (cf.clause.empty()) return std::nullopt;
    if (!normalizeTheoryClause(cf.clause)) return std::nullopt;
    return cf;
}

// Recognize lowered `m - 2^k*q - r = 0` (m coeff +1/-1, q coeff -/+2^k, r coeff
// -/+1 with r's sign == q's sign), bind r=m's low k bits, q=m's high bits.
// Sound because mod m 2^k = m's low k bits (two's complement, any sign) and the
// width-(maxk+1) model covers every residue, so the box is complete for the
// mod-by-2^k dividends and UNSAT is sound -- BUT only if the dividend appears
// ONLY in these groups (no raw use) and every other variable is hard-bounded.
std::optional<BitBlastResult> BitBlastSolver::tryBvDivMod(
    const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains,
    const IntegerModelValidator& validator) {

    static const bool DBG = std::getenv("ZOLVER_NIA_BV_DIVMOD_DEBUG") != nullptr;
    auto pow2k = [](const mpz_class& a) -> int {
        mpz_class v = abs(a);
        if (v < 2 || mpz_popcount(v.get_mpz_t()) != 1) return -1;
        return static_cast<int>(mpz_sizeinbase(v.get_mpz_t(), 2)) - 1;
    };

    struct Group { std::string dividend, quot, rem; unsigned k; };
    std::vector<Group> groups;
    std::vector<bool> definitional(cs.size(), false);

    for (size_t ci = 0; ci < cs.size(); ++ci) {
        if (cs[ci].rel != Relation::Eq) continue;
        auto termsOpt = kernel_.terms(cs[ci].poly);
        if (!termsOpt || termsOpt->size() != 3) continue;
        const PolynomialKernel::MonomialTerm *qT = nullptr, *u1 = nullptr, *u2 = nullptr;
        bool ok = true;
        for (const auto& t : *termsOpt) {
            if (t.powers.size() != 1 || t.powers[0].second != 1) { ok = false; break; }
            int k = pow2k(t.coefficient);
            if (k >= 1) { if (qT) { ok = false; break; } qT = &t; }
            else if (t.coefficient == 1 || t.coefficient == -1) {
                if (!u1) u1 = &t; else if (!u2) u2 = &t; else { ok = false; break; }
            } else { ok = false; break; }
        }
        if (!ok || !qT || !u1 || !u2) continue;
        bool qNeg = qT->coefficient < 0;
        const PolynomialKernel::MonomialTerm* rT = ((u1->coefficient < 0) == qNeg) ? u1 : u2;
        const PolynomialKernel::MonomialTerm* mT = (rT == u1) ? u2 : u1;
        if ((mT->coefficient < 0) == (rT->coefficient < 0)) continue;  // need opposite unit signs
        groups.push_back({std::string(kernel_.varName(mT->powers[0].first)),
                          std::string(kernel_.varName(qT->powers[0].first)),
                          std::string(kernel_.varName(rT->powers[0].first)),
                          static_cast<unsigned>(pow2k(qT->coefficient))});
        definitional[ci] = true;
    }
    if (DBG) std::cerr << "[BVDM] groups=" << groups.size() << "\n";
    if (groups.empty()) return std::nullopt;

    std::unordered_map<std::string, unsigned> maxK;
    std::unordered_set<std::string> dividends, qrset;
    for (const auto& g : groups) {
        unsigned cur = maxK.count(g.dividend) ? maxK[g.dividend] : 0u;
        maxK[g.dividend] = std::max(cur, g.k);
        dividends.insert(g.dividend);
        qrset.insert(g.quot); qrset.insert(g.rem);
    }
    for (const auto& d : dividends) if (qrset.count(d)) { if(DBG) std::cerr<<"[BVDM] bail: var both roles\n"; return std::nullopt; }

    // GUARD: dividend may appear only in the definitional groups (else a fixed
    // width unsoundly restricts an otherwise-unbounded dividend).
    std::unordered_set<std::string> allVars;
    for (size_t ci = 0; ci < cs.size(); ++ci) {
        for (const auto& v : kernel_.variables(cs[ci].poly)) {
            allVars.insert(v);
            if (!definitional[ci] && dividends.count(v)) { if(DBG) std::cerr<<"[BVDM] bail: dividend "<<v<<" raw use\n"; return std::nullopt; }
        }
    }
    // GUARD: every non-divmod variable must be hard-bounded (for box completeness).
    for (const auto& v : allVars) {
        if (dividends.count(v) || qrset.count(v)) continue;
        const IntDomain* d = domains.getDomain(v);
        if (!d || !d->hasLower || !d->hasUpper) { if(DBG) std::cerr<<"[BVDM] bail: nondivmod var "<<v<<" unbounded\n"; return std::nullopt; }
    }
    if (DBG) std::cerr << "[BVDM] applying: " << groups.size() << " groups\n";

    BitWidthPlan plan = estimator_.estimate(cs, domains);
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    enc.setVarBudget(gateBudget_);
    std::unordered_map<std::string, BitVec> varBits;
    for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);
    for (const auto& kv : maxK) varBits[kv.first] = enc.mkVar(kv.second + 1);  // dividend: maxk+1
    for (const auto& g : groups) {
        const BitVec& m = varBits[g.dividend];
        unsigned W = maxK[g.dividend] + 1;
        BitVec r; r.bits.assign(m.bits.begin(), m.bits.begin() + g.k);
        r.bits.push_back(enc.constFalse());        // low k bits, 0 sign => m mod 2^k >= 0
        varBits[g.rem] = r;
        BitVec q; q.bits.assign(m.bits.begin() + g.k, m.bits.begin() + W);   // high bits
        if (q.bits.empty()) q.bits.push_back(enc.constFalse());
        varBits[g.quot] = q;
    }

    PolyBitBlaster blaster(enc, kernel_, varBits);
    for (size_t ci = 0; ci < cs.size(); ++ci)
        if (!definitional[ci]) blaster.assertConstraint(cs[ci]);   // mod-Eqs are definitional via slices
    encodeDomainBounds(enc, varBits, domains);
    if (enc.overflowed()) return std::nullopt;

    BitBlastResult out;
    auto res = sat->solve();
    if (res == SatSolver::SolveResult::Sat) {
        IntegerModel model;
        for (const auto& kv : varBits) model[kv.first] = readBitVec(*sat, kv.second);
        if (validator.validate(model, cs) == IntegerModelValidator::Result::Valid
            && modelInDomains(model, domains)) {
            out.status = BitBlastResult::Status::Sat;
            out.model = std::move(model);
        }
        return out;                       // Sat, or Unknown if the model didn't validate
    }
    if (res == SatSolver::SolveResult::Unsat) {
        // Box is complete by construction (mod-2^k residues fully covered, other
        // vars hard-bounded), so this UNSAT is sound.
        if (auto cf = buildCompleteConflict(cs, domains)) out.status = BitBlastResult::Status::UnsatComplete, out.conflict = std::move(cf);
        return out;
    }
    return out;                           // SAT solver Unknown
}

// One encode+solve+validate attempt at a fixed width plan. Returns the raw
// outcome (Sat carries a validated in-box model; Unsat is box-dependent — the
// caller decides whether it is globally complete; Overflow = encoding exceeded
// the var budget). Factored so the start-small cascade and the
// estimator-grow path share identical encoding/validation logic.
BitBlastSolver::Attempt BitBlastSolver::attemptAtWidths(
    const BitWidthPlan& plan,
    const std::vector<NormalizedNiaConstraint>& cs,
    const DomainStore& domains,
    const IntegerModelValidator& validator) {
    Attempt a;
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    enc.setVarBudget(gateBudget_);   // hard cap: stop encoding before OOM
    std::unordered_map<std::string, BitVec> varBits;
    for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);

    PolyBitBlaster blaster(enc, kernel_, varBits);
    for (const auto& c : cs) blaster.assertConstraint(c);
    encodeDomainBounds(enc, varBits, domains);   // confine search to the box

    if (enc.overflowed()) { a.kind = Attempt::Overflow; return a; }

    auto res = sat->solve();
    if (res == SatSolver::SolveResult::Sat) {
        IntegerModel model;
        for (const auto& kv : varBits) model[kv.first] = readBitVec(*sat, kv.second);
        // Accept only a model that satisfies cs (exact) AND lies in the box.
        if (validator.validate(model, cs) == IntegerModelValidator::Result::Valid
            && modelInDomains(model, domains)) {
            a.kind = Attempt::Sat;
            a.model = std::move(model);
        }
        // else: SAT under narrow widths but not a real / in-box model — artifact (Unknown).
        return a;
    }
    if (res == SatSolver::SolveResult::Unsat) { a.kind = Attempt::Unsat; return a; }
    return a;   // SAT solver Unknown
}

BitBlastResult BitBlastSolver::solve(const std::vector<NormalizedNiaConstraint>& cs,
                                     const DomainStore& domains,
                                     const IntegerModelValidator& validator) {
    BitBlastResult out;
    if (cs.empty() || !applicable(cs)) return out;   // Unknown

    static const bool bvDivMod = std::getenv("ZOLVER_NIA_BV_DIVMOD") != nullptr;
    if (bvDivMod) {
        if (auto r = tryBvDivMod(cs, domains, validator)) return *r;
        // else fall through to the general encoder
    }

    BitWidthPlan full = estimator_.estimate(cs, domains);
    if (full.width.empty()) return out;              // Unknown

    // cvc5 solve-int-as-bv cascade (ZOLVER_NIA_BV_CASCADE): for problems with an
    // unbounded variable (boxIsComplete=false ⇒ pure SAT search, UNSAT not
    // provable here anyway), start every unbounded var at a TINY uniform width
    // (K=2) and escalate ×2. Small widths fail fast and keep the encoding under
    // the var budget; this catches the "solution fits in K bits" majority of
    // QF_NIA-sat that the estimator's heuristic initial width would over-widen
    // (and budget-overflow) on iteration 0. Bounded vars keep their exact width
    // so nothing about completeness changes. Sound: every SAT model is validated.
    static const bool cascade = std::getenv("ZOLVER_NIA_BV_CASCADE") != nullptr;
    if (cascade && !full.boxIsComplete) {
        std::unordered_set<std::string> bounded;
        for (const auto& kv : full.width) {
            const IntDomain* d = domains.getDomain(kv.first);
            if (d && d->hasLower && d->hasUpper) bounded.insert(kv.first);
        }
        unsigned K = 2;
        while (true) {
            BitWidthPlan plan;
            for (const auto& kv : full.width)
                plan.width[kv.first] = bounded.count(kv.first) ? kv.second
                                                               : std::min(K, maxBW_);
            Attempt a = attemptAtWidths(plan, cs, domains, validator);
            if (a.kind == Attempt::Sat) {
                out.status = BitBlastResult::Status::Sat;
                out.model = std::move(a.model);
                return out;
            }
            if (a.kind == Attempt::Overflow) break;   // larger K only worse
            if (K >= maxBW_) break;                   // reached the width ceiling
            K = std::min(K * 2, maxBW_);
        }
        return out;   // Unknown (box incomplete ⇒ never UnsatComplete here)
    }

    // Default path: estimator-sized widths + ×grow, with complete-box UnsatComplete.
    BitWidthPlan plan = full;
    for (unsigned iter = 0; iter < maxIters_; ++iter) {
        Attempt a = attemptAtWidths(plan, cs, domains, validator);
        if (a.kind == Attempt::Overflow) return out;   // incomplete encoding; widths only grow
        if (a.kind == Attempt::Sat) {
            out.status = BitBlastResult::Status::Sat;
            out.model = std::move(a.model);
            return out;
        }
        if (a.kind == Attempt::Unsat) {
            if (plan.boxIsComplete) {
                if (auto cf = buildCompleteConflict(cs, domains)) {
                    out.status = BitBlastResult::Status::UnsatComplete;
                    out.conflict = std::move(cf);
                }
                return out;   // complete box decided (UnsatComplete or Unknown if no reasons)
            }
            // Heuristic box UNSAT proves nothing globally: keep Unknown.
        } else {
            return out;       // SAT solver Unknown
        }

        if (plan.boxIsComplete) break;          // exact box already decided above
        plan = SpaceEstimator::grow(plan, maxBW_);   // x4 widen
    }
    return out;               // Unknown
}

} // namespace zolver::bitblast
