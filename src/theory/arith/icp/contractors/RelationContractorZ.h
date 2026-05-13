#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/interval/IntervalOperations.h"
#include <memory>

namespace nlcolver {

class RelationContractorZ : public ContractorZ {
public:
    RelationContractorZ(const IcpConstraint& constraint, PolynomialKernel& kernel);

    ContractorResultZ contract(ReasonedBoxZ& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::vector<std::string> vars_;

    bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) const;
};

} // namespace nlcolver
