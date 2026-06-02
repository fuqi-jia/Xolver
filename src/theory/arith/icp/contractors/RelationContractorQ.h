#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/poly/PolynomialKernel.h"

namespace xolver {

// Single-variable rational contractor — for NRA.
// V1: only detects definite violation via interval evaluation; no domain
// narrowing (NoChange status). The univariate restriction keeps soundness
// trivial: with one variable, intervalPow(IntervalQ) is exact for monomials
// and Σ is an over-approx, so any sign mismatch is definitive.
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
};

} // namespace xolver
