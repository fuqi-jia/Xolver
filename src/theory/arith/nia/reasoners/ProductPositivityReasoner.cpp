#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include <gmpxx.h>
#include <string>
#include <algorithm>
#include <unordered_set>
#include <unordered_map>

namespace xolver {

namespace {

using MonomialTerm = PolynomialKernel::MonomialTerm;

// Working constraint: `poly` may be rewritten by substitution; `extra`
// accumulates the reasons of every fixed-variable equality substituted into it,
// so any bound derived from this constraint carries a sound justification.
struct WorkC {
    PolyId poly;
    Relation rel;
    SatLit reason;
    std::vector<SatLit> extra;
};

std::vector<SatLit> baseReasons(const WorkC& wc) {
    std::vector<SatLit> r;
    r.push_back(wc.reason);
    r.insert(r.end(), wc.extra.begin(), wc.extra.end());
    return r;
}

// The NiaNormalizer emits constraints as `poly <= 0` (Leq) as well as `>= 0`
// (Geq). Return the terms in a >=0 / =0 oriented form so the rules below only
// reason about Geq: for Leq, negate every coefficient (poly<=0 <=> -poly>=0).
// Returns {terms, effectiveRel in {Geq,Eq}} or nullopt for relations the rules
// do not use (Neq) or when decomposition is unavailable.
std::optional<std::pair<std::vector<MonomialTerm>, Relation>>
geqNormalize(const PolynomialKernel& kernel, PolyId poly, Relation rel) {
    auto termsOpt = kernel.terms(poly);
    if (!termsOpt) return std::nullopt;
    std::vector<MonomialTerm> terms = std::move(*termsOpt);
    if (rel == Relation::Geq || rel == Relation::Eq) {
        return std::make_pair(std::move(terms), rel);
    }
    if (rel == Relation::Leq) {
        for (auto& t : terms) t.coefficient = -t.coefficient;
        return std::make_pair(std::move(terms), Relation::Geq);
    }
    return std::nullopt;
}

// True iff every factor variable of `mono` is known-nonnegative; appends each
// factor's nonneg lower-bound reasons to `reasons`.
bool factorsNonneg(const PolynomialKernel& kernel, const MonomialTerm& mono,
                   const DomainStore& domains, std::vector<SatLit>& reasons) {
    for (const auto& pe : mono.powers) {
        std::string vname(kernel.varName(pe.first));
        const IntDomain* d = domains.getDomain(vname);
        if (d == nullptr || !d->hasLower || d->lower.value < 0) return false;
        for (SatLit r : d->lower.reasons) reasons.push_back(r);
    }
    return true;
}

// True iff `v` is established strictly positive (>= 1, hence != 0). Appends the
// justifying reasons.
bool establishedNonzero(const PolynomialKernel& kernel, VarId v,
                        const DomainStore& domains, std::vector<SatLit>& reasons) {
    std::string vname(kernel.varName(v));
    const IntDomain* d = domains.getDomain(vname);
    if (d == nullptr || !d->hasLower || d->lower.value < 1) return false;
    for (SatLit r : d->lower.reasons) reasons.push_back(r);
    return true;
}

bool fixVar(DomainStore& domains, const std::string& var, const mpz_class& val,
            const std::vector<SatLit>& reasons, bool& change) {
    const IntDomain* d = domains.getDomain(var);
    bool already = d && d->hasLower && d->hasUpper &&
                   d->lower.value == val && d->upper.value == val;
    if (already) return false;
    domains.addLowerBound(var, val, reasons);
    domains.addUpperBound(var, val, reasons);
    change = true;
    return true;
}

// ---- Closer 2: substitute domain-FIXED variables into every working poly. --
// v fixed (lower==upper==val) is a proven equality v=val; substituting it is
// always sound. The fixed-var's reasons are carried onto each constraint it is
// substituted into. (A var is substituted at most once per constraint -- after
// substitution it no longer appears -- so `extra` cannot grow unboundedly.)
void substituteFixedVars(PolynomialKernel& kernel, std::vector<WorkC>& work,
                         const DomainStore& domains, bool& change) {
    // iter-110 perf: pre-compute each work constraint's variable SET once,
    // refreshed after substitution. Was calling kernel.variables(wc.poly)
    // + std::find per (fixed-var × work-constraint) pair → O(D × W × |vars|).
    // Now O(W × avg-|vars|) variable-collection up front; inner check O(1).
    // After a successful substitution the constraint's poly changed, so
    // refresh that single entry — `change` itself implies "iterate again"
    // so per-iteration the cache stays consistent with the polys.
    std::vector<std::unordered_set<std::string>> wcVarSet(work.size());
    for (size_t i = 0; i < work.size(); ++i) {
        auto vs = kernel.variables(work[i].poly);
        wcVarSet[i] = std::unordered_set<std::string>(vs.begin(), vs.end());
    }

    for (const auto& kv : domains.getAllDomains()) {
        const std::string& name = kv.first;
        const IntDomain& dom = kv.second;
        if (!(dom.hasLower && dom.hasUpper && dom.lower.value == dom.upper.value)) continue;
        auto vOpt = kernel.findVar(name);
        if (!vOpt) continue;
        mpq_class val(dom.lower.value);
        std::vector<SatLit> rs = dom.lower.reasons;
        rs.insert(rs.end(), dom.upper.reasons.begin(), dom.upper.reasons.end());
        for (size_t i = 0; i < work.size(); ++i) {
            auto& wc = work[i];
            if (!wcVarSet[i].count(name)) continue;
            auto np = kernel.substituteRational(wc.poly, *vOpt, val);
            if (np && *np != wc.poly) {
                wc.poly = *np;
                wc.extra.insert(wc.extra.end(), rs.begin(), rs.end());
                change = true;
                // Refresh cache for this constraint; the substituted name is
                // gone and other vars may have collapsed.
                auto vs = kernel.variables(wc.poly);
                wcVarSet[i] = std::unordered_set<std::string>(vs.begin(), vs.end());
            }
        }
    }
}

// ---- Constant contradiction: a (substituted) constraint whose poly is a -----
// constant k violating its relation (e.g. -1 >= 0, or 1 = 0) is an immediate
// sound UNSAT; the conflict clause is the constraint plus the substitutions
// that produced the constant.
std::optional<NiaReasoningResult> checkConstantContradiction(
    PolynomialKernel& kernel, const std::vector<WorkC>& work) {
    for (const auto& c : work) {
        if (!kernel.isConstant(c.poly)) continue;
        mpq_class k = kernel.toConstant(c.poly);
        bool violated = false;
        switch (c.rel) {
            case Relation::Geq: violated = (k < 0); break;
            case Relation::Eq:  violated = (k != 0); break;
            case Relation::Leq: violated = (k > 0); break;
            case Relation::Neq: violated = (k == 0); break;
            default: break;
        }
        if (violated) {
            return NiaReasoningResult{NiaReasoningKind::Conflict,
                                      TheoryConflict{baseReasons(c)}, std::nullopt};
        }
    }
    return std::nullopt;
}

// ---- Rule A: sign-absorption / product-positivity -------------------------
std::optional<NiaReasoningResult> applySignAbsorption(
    PolynomialKernel& kernel, const std::vector<WorkC>& work,
    DomainStore& domains, bool& change) {

    for (const auto& c : work) {
        auto g = geqNormalize(kernel, c.poly, c.rel);
        if (!g) continue;
        const std::vector<MonomialTerm>& terms = g->first;
        const Relation eff = g->second;

        const MonomialTerm* pos = nullptr;
        int posCount = 0, nonConstCount = 0;
        mpz_class constTerm = 0;
        for (const auto& t : terms) {
            if (t.powers.empty()) { constTerm += t.coefficient; continue; }
            ++nonConstCount;
            if (t.coefficient > 0) { pos = &t; ++posCount; }
        }

        if (eff == Relation::Eq) {
            if (nonConstCount != 1 || posCount != 1) continue;
        } else {
            if (posCount != 1 || pos == nullptr) continue;
        }

        std::vector<SatLit> reasons = baseReasons(c);

        // adjust = sum over absorbed monomials |cj| * lb(mj), where lb(mj) is the
        // product of factor lower bounds. Since mj >= lb(mj) >= 0, this only
        // strengthens the bound on the positive monomial (M+ >= -d + adjust).
        mpz_class adjust = 0;
        if (eff == Relation::Geq) {
            bool ok = true;
            for (const auto& t : terms) {
                if (t.powers.empty() || &t == pos) continue;
                if (!factorsNonneg(kernel, t, domains, reasons)) { ok = false; break; }
                mpz_class lb = 1;
                for (const auto& pe : t.powers) {
                    const IntDomain* d = domains.getDomain(std::string(kernel.varName(pe.first)));
                    mpz_class p;
                    mpz_pow_ui(p.get_mpz_t(), d->lower.value.get_mpz_t(),
                               static_cast<unsigned long>(pe.second));
                    lb *= p;
                }
                adjust += (-t.coefficient) * lb;   // |cj| * lb(mj)
            }
            if (!ok) continue;
        }

        const mpz_class& cM = pos->coefficient;
        mpz_class rhs = -constTerm + adjust, L;
        if (eff == Relation::Geq) {
            mpz_cdiv_q(L.get_mpz_t(), rhs.get_mpz_t(), cM.get_mpz_t());
        } else {
            if (!mpz_divisible_p(rhs.get_mpz_t(), cM.get_mpz_t())) continue;
            L = rhs / cM;
        }
        if (L < 1) continue;
        if (!factorsNonneg(kernel, *pos, domains, reasons)) continue;

        for (const auto& pe : pos->powers) {
            std::string vname(kernel.varName(pe.first));
            const IntDomain* d = domains.getDomain(vname);
            if (d == nullptr || !d->hasLower || d->lower.value < 1) {
                domains.addLowerBound(vname, mpz_class(1), reasons);
                change = true;
            }
            if (domains.isEmpty(vname)) {
                return NiaReasoningResult{NiaReasoningKind::Conflict,
                                          domains.buildEmptyDomainConflict(), std::nullopt};
            }
        }
    }
    return std::nullopt;
}

// ---- Closer 1: equality common-factor cancellation ------------------------
std::optional<NiaReasoningResult> applyEqCancellation(
    PolynomialKernel& kernel, const std::vector<WorkC>& work,
    DomainStore& domains, bool& change) {

    for (const auto& c : work) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        if (terms.size() < 2) continue;

        bool hasConst = false;
        for (const auto& t : terms) if (t.powers.empty()) { hasConst = true; break; }
        if (hasConst) continue;

        std::unordered_set<VarId> common;
        for (const auto& pe : terms[0].powers) common.insert(pe.first);
        for (size_t i = 1; i < terms.size() && !common.empty(); ++i) {
            std::unordered_set<VarId> here;
            for (const auto& pe : terms[i].powers) here.insert(pe.first);
            for (auto it = common.begin(); it != common.end();)
                it = here.count(*it) ? std::next(it) : common.erase(it);
        }
        if (common.empty()) continue;

        for (VarId v : common) {
            std::vector<SatLit> reasons = baseReasons(c);
            if (!establishedNonzero(kernel, v, domains, reasons)) continue;

            mpz_class qConst = 0;
            std::vector<MonomialTerm> reduced;
            reduced.reserve(terms.size());
            for (const auto& t : terms) {
                MonomialTerm rt;
                rt.coefficient = t.coefficient;
                bool removed = false;
                for (const auto& pe : t.powers) {
                    if (pe.first == v && !removed) {
                        if (pe.second > 1) rt.powers.emplace_back(pe.first, pe.second - 1);
                        removed = true;
                    } else {
                        rt.powers.push_back(pe);
                    }
                }
                reduced.push_back(std::move(rt));
            }
            std::vector<const MonomialTerm*> qNonConst;
            for (const auto& rt : reduced) {
                if (rt.powers.empty()) qConst += rt.coefficient;
                else qNonConst.push_back(&rt);
            }

            if (qNonConst.size() != 1) continue;
            const MonomialTerm& m = *qNonConst[0];
            if (m.powers.size() != 1 || m.powers[0].second != 1) continue;
            const mpz_class& cw = m.coefficient;
            if (!mpz_divisible_p(qConst.get_mpz_t(), cw.get_mpz_t())) continue;
            mpz_class val = -qConst / cw;

            std::string wname(kernel.varName(m.powers[0].first));
            fixVar(domains, wname, val, reasons, change);
            if (domains.isEmpty(wname)) {
                return NiaReasoningResult{NiaReasoningKind::Conflict,
                                          domains.buildEmptyDomainConflict(), std::nullopt};
            }
            break;
        }
    }
    return std::nullopt;
}

// ---- Closer 3: monomial dominance -> Conflict -----------------------------
// Geq sum(ci*mi)+d>=0 with d<0. Pair each positive monomial P (coeff cP>0) with
// a distinct negative monomial N (coeff -|cN|) whose monomial value equals P*E,
// where every extra factor in E is established >=1 AND base P>=0 is established
// AND |cN|>=cP. Then cP*P - |cN|*N = cP*P - |cN|*P*E <= (cP-|cN|)*P <= 0. If all
// positives are dominated and every remaining negative monomial is >=0, then
// LHS <= d < 0, contradicting >=0 -> sound UNSAT.
// SOUNDNESS GUARD: base P>=0 is mandatory -- if P<0 then P*E<=P (the inequality
// FLIPS) and the bound is false. Established from the domain, never assumed.
std::optional<NiaReasoningResult> applyDominance(
    PolynomialKernel& kernel, const std::vector<WorkC>& work, const DomainStore& domains) {

    for (const auto& c : work) {
        auto g = geqNormalize(kernel, c.poly, c.rel);
        if (!g || g->second != Relation::Geq) continue;
        const std::vector<MonomialTerm>& terms = g->first;

        std::vector<const MonomialTerm*> pos, neg;
        mpz_class d = 0;
        for (const auto& t : terms) {
            if (t.powers.empty()) { d += t.coefficient; continue; }
            if (t.coefficient > 0) pos.push_back(&t); else neg.push_back(&t);
        }
        if (d >= 0) continue;  // need LHS bounded above by a negative constant

        std::vector<char> used(neg.size(), 0);
        std::vector<SatLit> reasons = baseReasons(c);
        bool ok = true;

        for (const MonomialTerm* P : pos) {
            // GUARD: base monomial must be established >= 0.
            if (!factorsNonneg(kernel, *P, domains, reasons)) { ok = false; break; }
            std::unordered_map<VarId, int> pmap;
            for (const auto& pe : P->powers) pmap[pe.first] += pe.second;

            bool found = false;
            for (size_t i = 0; i < neg.size(); ++i) {
                if (used[i]) continue;
                const MonomialTerm& N = *neg[i];
                if (-N.coefficient < P->coefficient) continue;   // need |cN| >= cP

                std::unordered_map<VarId, int> nmap;
                for (const auto& pe : N.powers) nmap[pe.first] += pe.second;

                bool dominates = true;                            // N's powers >= P's powers
                for (const auto& kv : pmap) {
                    auto it = nmap.find(kv.first);
                    if (it == nmap.end() || it->second < kv.second) { dominates = false; break; }
                }
                if (!dominates) continue;

                std::vector<SatLit> extra;                        // extra factors E = N \ P
                bool extrasOk = true;
                for (const auto& kv : nmap) {
                    int pe = pmap.count(kv.first) ? pmap[kv.first] : 0;
                    if (kv.second - pe > 0 &&
                        !establishedNonzero(kernel, kv.first, domains, extra)) {
                        extrasOk = false; break;
                    }
                }
                if (!extrasOk) continue;

                reasons.insert(reasons.end(), extra.begin(), extra.end());
                used[i] = 1;
                found = true;
                break;
            }
            if (!found) { ok = false; break; }
        }
        if (!ok) continue;

        // Every remaining (unpaired) negative monomial must be >= 0.
        for (size_t i = 0; i < neg.size() && ok; ++i)
            if (!used[i] && !factorsNonneg(kernel, *neg[i], domains, reasons)) ok = false;
        if (!ok) continue;

        return NiaReasoningResult{NiaReasoningKind::Conflict,
                                  TheoryConflict{reasons}, std::nullopt};
    }
    return std::nullopt;
}

} // namespace

ProductPositivityReasoner::ProductPositivityReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult ProductPositivityReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints, DomainStore& domains) {

    std::vector<WorkC> work;
    work.reserve(constraints.size());
    for (const auto& c : constraints) work.push_back({c.poly, c.rel, c.reason, {}});

    bool anyChange = false;
    constexpr int kMaxIters = 32;
    for (int iter = 0; iter < kMaxIters; ++iter) {
        bool iterChange = false;
        substituteFixedVars(kernel_, work, domains, iterChange);
        if (auto r = checkConstantContradiction(kernel_, work)) return *r;
        if (auto r = applySignAbsorption(kernel_, work, domains, iterChange)) return *r;
        if (auto r = applyEqCancellation(kernel_, work, domains, iterChange)) return *r;
        if (auto r = applyDominance(kernel_, work, domains)) return *r;
        anyChange |= iterChange;
        if (!iterChange) break;
    }

    return {anyChange ? NiaReasoningKind::DomainUpdated : NiaReasoningKind::NoChange,
            std::nullopt, std::nullopt};
}

} // namespace xolver
