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
};

} // namespace xolver
