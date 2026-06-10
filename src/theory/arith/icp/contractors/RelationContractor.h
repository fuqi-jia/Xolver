#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/interval/IntervalOperations.h"
#include <memory>

namespace xolver {

class RelationContractor : public Contractor {
public:
    RelationContractor(const IcpConstraint& constraint, PolynomialKernel& kernel);

    ContractorResultZ contract(ReasonedBox& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::vector<std::string> vars_;

    bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) const;
};

} // namespace xolver
