#pragma once

#include "theory/arith/kernel/icp/Contractor.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <vector>
#include <unordered_map>

namespace xolver {

// V7 — multivariate Cauchy bound for dense polynomials.
//
// Targets polynomials of the shape:
//     a · liveVar^d  +  Σ_{0 ≤ k < d} B_k(rest) · liveVar^k   rel  0
// where
//   - a is a scalar integer coefficient (no rest factors in pure live^d
//     terms; mixed live^d terms disqualify),
//   - d ≥ 2,
//   - each B_k(rest) is a polynomial in non-live vars, evaluated to an
//     interval value over the runtime rest-box.
//
// The constraint must depend on at least one non-leading live exponent
// (i.e., some k < d has a non-trivial B_k); otherwise V4 handles the
// pure-monomial case tighter and V7 declines. V5b handles d == 2 with
// tight discriminant bounds; V7 fires for d ≥ 3 when V4 declines.
//
// Math: Cauchy's bound is sound for every realization of (rest) values
// inside the rest box, so the realization-independent bound
//     M = 1 + max_k (max(|B_k.lo|, |B_k.hi|) / |a|)
// upper-bounds |x| for every real root across all (rest) realizations.
// Parity-aware case-split as in V5d:
//   - Eq:                   bracket [-M, M]
//   - Leq, a > 0, d even:   bracket [-M, M]
//   - Leq, a > 0, d odd:    upper x ≤ M only (p → -∞ on left)
//   - Geq, a > 0, d even:   skip (union)
//   - Geq, a > 0, d odd:    lower x ≥ -M only
// Sign-flip on relation for a < 0.
//
// Looser than V4/V5b/V5c but covers shapes those can't (e.g.
// a·x³ + B(y)·x² + C(y)·x + D(y) ≤ 0).
class MultivariateCauchyContractorQ : public ContractorQ {
public:
    MultivariateCauchyContractorQ(
        const IcpConstraint& constraint,
        PolynomialKernel& kernel,
        const std::string& liveVar);

    bool isUsable() const { return usable_; }

    ContractorResultQ contract(ReasonedBoxQ& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::string liveVar_;
    std::vector<std::string> allVars_;

    bool usable_ = false;
    unsigned liveD_ = 0;
    mpz_class liveA_;
    // Per-live-exponent terms (key = live exponent 0 ≤ k < d). Each list
    // collects the terms whose live-power equals k; evaluated over the
    // rest box at contract() time to give an interval-valued coefficient.
    std::unordered_map<unsigned, std::vector<PolynomialKernel::MonomialTerm>>
        nonLeadingTermsByExp_;

    std::optional<IntervalQ> evalTermsAtExp(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const ReasonedBoxQ& box,
        std::vector<SatLit>& usedReasons,
        VarId liveVarId) const;
};

} // namespace xolver
