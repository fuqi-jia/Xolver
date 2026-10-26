#pragma once

#include "search/icp/Contractor.h"
#include "algebra/poly/PolynomialKernel.h"
#include "algebra/interval/IntervalOperations.h"
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
    std::optional<std::vector<PolynomialKernel::MonomialTerm>> terms_;
    std::vector<std::pair<VarId, mpz_class>> projections_;

    bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) const;
};

} // namespace xolver
