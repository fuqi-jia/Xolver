#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include <gmpxx.h>
#include <string>

namespace zolver {

ProductPositivityReasoner::ProductPositivityReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult ProductPositivityReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints, DomainStore& domains) {

    bool changed = false;

    for (const auto& c : constraints) {
        // Milestone 1: only Geq (p >= 0) and Eq (p = 0).
        if (c.rel != Relation::Geq && c.rel != Relation::Eq) continue;

        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;

        // Require exactly one non-constant monomial M, plus an optional constant.
        const PolynomialKernel::MonomialTerm* mono = nullptr;
        mpz_class constTerm = 0;
        int nonConstCount = 0;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) {
                constTerm += t.coefficient;
            } else {
                mono = &t;
                ++nonConstCount;
            }
        }
        if (nonConstCount != 1 || mono == nullptr) continue;

        // Constraint is  cM*M + constTerm  REL  0   <=>   cM*M  REL  -constTerm.
        // We can only derive a *lower* bound M >= L when the monomial coefficient
        // is positive.
        const mpz_class& cM = mono->coefficient;
        if (cM <= 0) continue;

        mpz_class rhs = -constTerm;   // cM*M REL rhs
        mpz_class L;
        if (c.rel == Relation::Geq) {
            // cM*M >= rhs, cM > 0  ->  M >= ceil(rhs / cM)
            mpz_cdiv_q(L.get_mpz_t(), rhs.get_mpz_t(), cM.get_mpz_t());
        } else { // Eq: cM*M = rhs  ->  M = rhs/cM, only if divisible
            if (!mpz_divisible_p(rhs.get_mpz_t(), cM.get_mpz_t())) continue;
            L = rhs / cM;
        }

        // Need M >= 1 to conclude every (nonneg) factor is >= 1.
        if (L < 1) continue;

        // Soundness guard: EVERY factor variable must be known-nonnegative.
        // (If a factor could be negative, M >= 1 does not force that factor >= 1.)
        // Collect the justifying reasons: the constraint itself plus each
        // factor's nonneg lower-bound reasons (omitting any yields an
        // over-strong, unsound conflict clause).
        std::vector<SatLit> reasons;
        reasons.push_back(c.reason);
        bool allNonneg = true;
        for (const auto& pe : mono->powers) {
            std::string vname(kernel_.varName(pe.first));
            const IntDomain* d = domains.getDomain(vname);
            if (d == nullptr || !d->hasLower || d->lower.value < 0) {
                allNonneg = false;
                break;
            }
            for (SatLit r : d->lower.reasons) reasons.push_back(r);
        }
        if (!allNonneg) continue;

        // Apply: each factor variable >= 1 (sound: any factor = 0 makes M = 0 < 1).
        for (const auto& pe : mono->powers) {
            std::string vname(kernel_.varName(pe.first));
            const IntDomain* d = domains.getDomain(vname);
            if (d == nullptr || !d->hasLower || d->lower.value < 1) {
                domains.addLowerBound(vname, mpz_class(1), reasons);
                changed = true;
            }
            if (domains.isEmpty(vname)) {
                return {NiaReasoningKind::Conflict,
                        domains.buildEmptyDomainConflict(), std::nullopt};
            }
        }
    }

    return {changed ? NiaReasoningKind::DomainUpdated : NiaReasoningKind::NoChange,
            std::nullopt, std::nullopt};
}

} // namespace zolver
