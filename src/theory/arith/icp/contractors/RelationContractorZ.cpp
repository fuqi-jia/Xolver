#include "theory/arith/icp/contractors/RelationContractorZ.h"
#include <algorithm>

namespace nlcolver {

RelationContractorZ::RelationContractorZ(const IcpConstraint& constraint, PolynomialKernel& kernel)
    : constraint_(constraint), kernel_(kernel) {
    vars_ = kernel_.variables(constraint_.poly);
}

ContractorResultZ RelationContractorZ::contract(ReasonedBoxZ& box) {
    // Multivar safeguard: if more than one variable, we cannot soundly eval interval
    if (vars_.size() != 1) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const std::string& var = vars_[0];
    auto riOpt = box.get(var);
    if (!riOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto degOpt = kernel_.degree(constraint_.poly, var);
    if (!degOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint_.poly, var);
    if (!coeffsOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const auto& coeffs = *coeffsOpt;
    const IntervalZ& xInterval = riOpt->interval;

    // Evaluate polynomial at interval
    IntervalZ result{mpz_class(0), mpz_class(0)};
    for (size_t i = 0; i < coeffs.size(); ++i) {
        const mpz_class& coeff = coeffs[i];
        if (coeff == 0) continue;
        size_t power = coeffs.size() - 1 - i;
        IntervalZ termInterval = intervalPow(xInterval, static_cast<uint32_t>(power));
        if (coeff != 1) {
            IntervalZ coeffInterval{coeff, coeff};
            termInterval = intervalMul(coeffInterval, termInterval);
        }
        result = intervalAdd(result, termInterval);
    }

    // Collect reasons
    std::vector<SatLit> reasons = riOpt->reasons;
    reasons.push_back(constraint_.reason);

    if (isDefinitelyViolated(result, constraint_.rel)) {
        return ContractorResultZ{
            IcpStatus::Conflict,
            TheoryConflict{reasons},
            {}
        };
    }

    return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
}

std::vector<std::string> RelationContractorZ::vars() const {
    return vars_;
}

SatLit RelationContractorZ::reason() const {
    return constraint_.reason;
}

bool RelationContractorZ::isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) const {
    switch (rel) {
        case Relation::Leq:
            return polyInterval.lo > 0;
        case Relation::Geq:
            return polyInterval.hi < 0;
        case Relation::Eq:
            return !polyInterval.containsZero();
        case Relation::Neq:
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false; // Lt/Gt: V1 not handled here (normalized before ICP for NIA, NoChange for NRA)
    }
}

} // namespace nlcolver
