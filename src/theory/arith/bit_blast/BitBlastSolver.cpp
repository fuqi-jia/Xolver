#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "sat/SatSolver.h"
#include <cstdlib>
#include <string>
#include <unordered_map>

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

BitBlastResult BitBlastSolver::solve(const std::vector<NormalizedNiaConstraint>& cs,
                                     const DomainStore& domains,
                                     const IntegerModelValidator& validator) {
    BitBlastResult out;
    if (cs.empty() || !applicable(cs)) return out;   // Unknown

    BitWidthPlan plan = estimator_.estimate(cs, domains);
    if (plan.width.empty()) return out;              // Unknown

    for (unsigned iter = 0; iter < maxIters_; ++iter) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        enc.setVarBudget(gateBudget_);   // hard cap: stop encoding before OOM
        std::unordered_map<std::string, BitVec> varBits;
        for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);

        PolyBitBlaster blaster(enc, kernel_, varBits);
        for (const auto& c : cs) blaster.assertConstraint(c);
        encodeDomainBounds(enc, varBits, domains);   // confine search to the box

        // Resource guard: the encoding exceeded the variable budget (high-degree
        // blow-up). The partial encoding is incomplete, so we must NOT solve it.
        // Widths only grow, so larger iterations are worse — bail to Unknown
        // (sound; other NIA stages still run).
        if (enc.overflowed()) return out;

        auto res = sat->solve();
        if (res == SatSolver::SolveResult::Sat) {
            IntegerModel model;
            for (const auto& kv : varBits) model[kv.first] = readBitVec(*sat, kv.second);
            // Accept only a model that satisfies cs (exact) AND lies in the box.
            if (validator.validate(model, cs) == IntegerModelValidator::Result::Valid
                && modelInDomains(model, domains)) {
                out.status = BitBlastResult::Status::Sat;
                out.model = std::move(model);
                return out;
            }
            // SAT under narrow widths but not a real / in-box model: artifact.
        } else if (res == SatSolver::SolveResult::Unsat) {
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
        plan = SpaceEstimator::grow(plan, maxBW_);   // doubling widen
    }
    return out;               // Unknown
}

} // namespace zolver::bitblast
