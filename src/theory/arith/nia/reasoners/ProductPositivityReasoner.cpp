#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include <gmpxx.h>
#include <string>
#include <unordered_set>

namespace zolver {

namespace {

using MonomialTerm = PolynomialKernel::MonomialTerm;

// True iff every factor variable of `mono` is known-nonnegative in `domains`.
// Appends each factor's nonneg lower-bound reasons to `reasons` (needed so the
// derived bound's eventual empty-domain conflict clause is not over-strong).
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

// True iff `v` is established strictly positive (>= 1, hence != 0) in domains.
// Appends the justifying reasons.
bool establishedNonzero(const PolynomialKernel& kernel, VarId v,
                        const DomainStore& domains, std::vector<SatLit>& reasons) {
    std::string vname(kernel.varName(v));
    const IntDomain* d = domains.getDomain(vname);
    if (d == nullptr || !d->hasLower || d->lower.value < 1) return false;
    for (SatLit r : d->lower.reasons) reasons.push_back(r);
    return true;
}

// Set `var` to the fixed value `val`. Returns true iff this tightened the
// domain (so the fixpoint makes progress only on real change).
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

// ---- Rule A: sign-absorption / product-positivity -------------------------
// Geq sum(ci*mi)+d>=0 with exactly one positive-coeff monomial M+ and every
// other non-constant monomial negative-coeff with nonneg factors: the negatives
// are absorbed, so c+*M+ >= -d, hence M+ >= ceil(-d/c+). If >= 1 and every
// factor of M+ is known-nonneg, each factor >= 1. Eq handles only the single
// (positive) monomial case. Sets `change`; returns a Conflict result or nullopt.
std::optional<NiaReasoningResult> applySignAbsorption(
    PolynomialKernel& kernel, const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains, bool& change) {

    for (const auto& c : constraints) {
        if (c.rel != Relation::Geq && c.rel != Relation::Eq) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;

        const MonomialTerm* pos = nullptr;
        int posCount = 0, nonConstCount = 0;
        mpz_class constTerm = 0;
        for (const auto& t : terms) {
            if (t.powers.empty()) { constTerm += t.coefficient; continue; }
            ++nonConstCount;
            if (t.coefficient > 0) { pos = &t; ++posCount; }
        }

        if (c.rel == Relation::Eq) {
            if (nonConstCount != 1 || posCount != 1) continue;
        } else {
            if (posCount != 1 || pos == nullptr) continue;
        }

        std::vector<SatLit> reasons;
        reasons.push_back(c.reason);

        if (c.rel == Relation::Geq) {
            bool ok = true;
            for (const auto& t : terms) {
                if (t.powers.empty() || &t == pos) continue;
                if (!factorsNonneg(kernel, t, domains, reasons)) { ok = false; break; }
            }
            if (!ok) continue;
        }

        const mpz_class& cM = pos->coefficient;
        mpz_class rhs = -constTerm, L;
        if (c.rel == Relation::Geq) {
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

// ---- Rule B (closer 1): equality common-factor cancellation ---------------
// a*f = 0 with a established != 0  ==>  f = 0.  Concretely: an Eq whose every
// monomial shares a variable v that is established nonzero (v>=1); cancel one
// power of v from each monomial. If the quotient is linear-univariate c*w + d,
// derive w = -d/c. Sound only because v != 0 is *established*, never assumed.
std::optional<NiaReasoningResult> applyEqCancellation(
    PolynomialKernel& kernel, const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains, bool& change) {

    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        if (terms.size() < 2) continue;

        // A constant term cannot share a variable factor -> no common var.
        bool hasConst = false;
        for (const auto& t : terms) if (t.powers.empty()) { hasConst = true; break; }
        if (hasConst) continue;

        // Common variables = present (exp>=1) in EVERY monomial.
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
            std::vector<SatLit> reasons;
            reasons.push_back(c.reason);
            if (!establishedNonzero(kernel, v, domains, reasons)) continue;

            // Quotient poly/v: decrement one power of v in each monomial.
            mpz_class qConst = 0;
            std::vector<const MonomialTerm*> qNonConst;
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
            for (const auto& rt : reduced) {
                if (rt.powers.empty()) qConst += rt.coefficient;
                else qNonConst.push_back(&rt);
            }

            // Only the linear-univariate quotient  cw*w + d = 0  is handled.
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
            break;  // one cancellation per constraint per sweep
        }
    }
    return std::nullopt;
}

} // namespace

ProductPositivityReasoner::ProductPositivityReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult ProductPositivityReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints, DomainStore& domains) {

    bool anyChange = false;
    constexpr int kMaxIters = 32;   // bounded fixpoint (monotone bound tightening)
    for (int iter = 0; iter < kMaxIters; ++iter) {
        bool iterChange = false;
        if (auto r = applySignAbsorption(kernel_, constraints, domains, iterChange)) return *r;
        if (auto r = applyEqCancellation(kernel_, constraints, domains, iterChange)) return *r;
        anyChange |= iterChange;
        if (!iterChange) break;
    }

    return {anyChange ? NiaReasoningKind::DomainUpdated : NiaReasoningKind::NoChange,
            std::nullopt, std::nullopt};
}

} // namespace zolver
