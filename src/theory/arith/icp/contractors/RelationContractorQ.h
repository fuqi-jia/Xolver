#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <optional>

namespace xolver {

// Single-variable rational contractor — for NRA.
//
// V1 — definite-violation detection via Horner interval evaluation.
//   The univariate restriction keeps soundness trivial: intervalPow on
//   IntervalQ is exact for monomials and Σ is a sound over-approx, so any
//   sign mismatch with the asserted relation is definitive.
//
// V2 — quadratic inversion narrowing for `ax²+bx+c rel 0` with rel ∈
//   {Leq, Lt} and a > 0. The feasible set is the closed interval [r1, r2]
//   between the real roots (or empty if disc < 0). We narrow x's box to an
//   outward-rounded over-approximation of [r1, r2]. Other (rel, sign-of-a)
//   combinations yield a union of intervals which IntervalQ can't represent;
//   we skip them (coverage gap, not soundness gap).
class RelationContractorQ : public ContractorQ {
public:
    RelationContractorQ(const IcpConstraint& constraint, PolynomialKernel& kernel);

    ContractorResultQ contract(ReasonedBoxQ& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::vector<std::string> vars_;

    bool isDefinitelyViolated(const IntervalQ& polyInterval, Relation rel) const;

    // V2: returns nullopt if not applicable (rel ∉ {Leq, Lt}, degree ≠ 2,
    // a ≤ 0). Returns an empty IntervalQ (lo > hi) to signal "constraint
    // unsatisfiable for any x" (disc < 0). Returns a well-formed interval as
    // the outward-rounded feasible-set over-approximation.
    std::optional<IntervalQ> tryNarrowDeg2(const std::vector<mpz_class>& coeffs,
                                           Relation rel) const;

    // V3a: pure-monomial sign narrowing for a·x^d with d ≥ 3. (V2 handles
    // d == 2 strictly better via discriminant; this helper guards d ≥ 3.)
    //
    // Even d: x^d ≥ 0, so the feasible set collapses based on the constant
    // side of `rel` (Leq/Eq narrow to {0}; Lt is unsatisfiable; Geq/Gt/Neq
    // either always-true or x ≠ 0 which is not single-interval).
    //
    // Odd d: sign(x^d) = sign(x), so the feasible set is a half-line that
    // becomes a closed interval after intersection with xBox.
    //
    // Returns nullopt if not applicable. An empty IntervalQ signals a
    // conflict. A non-empty IntervalQ is the result ALREADY intersected
    // with xBox — caller only checks identity vs xBox for change detection.
    std::optional<IntervalQ> tryNarrowPureMonomial(
        const std::vector<mpz_class>& coeffs, Relation rel,
        const IntervalQ& xBox) const;
};

} // namespace xolver
