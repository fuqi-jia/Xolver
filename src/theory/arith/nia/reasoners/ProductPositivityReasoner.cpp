#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include <gmpxx.h>
#include <string>

namespace zolver {

ProductPositivityReasoner::ProductPositivityReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

namespace {

// True iff every factor variable of `mono` is known-nonnegative in `domains`.
// Appends each factor's nonneg lower-bound reasons to `reasons` (needed so the
// derived bound's eventual empty-domain conflict clause is not over-strong).
bool factorsNonneg(const PolynomialKernel& kernel,
                   const PolynomialKernel::MonomialTerm& mono,
                   const DomainStore& domains,
                   std::vector<SatLit>& reasons) {
    for (const auto& pe : mono.powers) {
        std::string vname(kernel.varName(pe.first));
        const IntDomain* d = domains.getDomain(vname);
        if (d == nullptr || !d->hasLower || d->lower.value < 0) return false;
        for (SatLit r : d->lower.reasons) reasons.push_back(r);
    }
    return true;
}

} // namespace

NiaReasoningResult ProductPositivityReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints, DomainStore& domains) {

    bool changed = false;

    for (const auto& c : constraints) {
        if (c.rel != Relation::Geq && c.rel != Relation::Eq) continue;

        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;

        // Partition: constant term, the (hopefully unique) positive-coefficient
        // monomial, and the remaining non-constant monomials.
        const PolynomialKernel::MonomialTerm* pos = nullptr;
        int posCount = 0;
        int nonConstCount = 0;
        mpz_class constTerm = 0;
        for (const auto& t : terms) {
            if (t.powers.empty()) { constTerm += t.coefficient; continue; }
            ++nonConstCount;
            if (t.coefficient > 0) { pos = &t; ++posCount; }
        }

        // ----- Eq: only the single-monomial case is unambiguous -----
        // (c*M + d = 0 -> M = -d/c if integral; multi-monomial equalities give
        // no clean lower bound without bounds on the other monomials.)
        if (c.rel == Relation::Eq) {
            if (nonConstCount != 1 || pos == nullptr) continue;
            // pos here is the lone monomial only if its coeff > 0; a negative
            // lone coefficient cannot yield a positive lower bound.
            if (posCount != 1) continue;
        } else {
            // ----- Geq: sign-absorption. Need exactly one positive monomial; -----
            // every other non-constant monomial must be negative-coeff with
            // all-nonneg factors (so it is >= 0 and only weakens the bound).
            if (posCount != 1 || pos == nullptr) continue;
        }

        const mpz_class& cM = pos->coefficient;   // > 0 by construction
        std::vector<SatLit> reasons;
        reasons.push_back(c.reason);

        // Every absorbed monomial (Geq, the non-positive ones) must be nonneg.
        bool ok = true;
        if (c.rel == Relation::Geq) {
            for (const auto& t : terms) {
                if (t.powers.empty() || &t == pos) continue;
                if (!factorsNonneg(kernel_, t, domains, reasons)) { ok = false; break; }
            }
            if (!ok) continue;
        }

        // M = pos monomial.  Constraint gives  cM * M  REL  -constTerm.
        mpz_class rhs = -constTerm;
        mpz_class L;
        if (c.rel == Relation::Geq) {
            mpz_cdiv_q(L.get_mpz_t(), rhs.get_mpz_t(), cM.get_mpz_t());  // M >= ceil(rhs/cM)
        } else { // Eq
            if (!mpz_divisible_p(rhs.get_mpz_t(), cM.get_mpz_t())) continue;
            L = rhs / cM;
        }
        if (L < 1) continue;  // need M >= 1 to force each (nonneg) factor >= 1

        // The positive monomial's own factors must be known-nonneg.
        if (!factorsNonneg(kernel_, *pos, domains, reasons)) continue;

        for (const auto& pe : pos->powers) {
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
