#include "theory/arith/icp/contractors/RelationContractorQ.h"
#include "theory/arith/interval/IntervalQOps.h"

namespace xolver {

RelationContractorQ::RelationContractorQ(const IcpConstraint& constraint, PolynomialKernel& kernel)
    : constraint_(constraint), kernel_(kernel) {
    vars_ = kernel_.variables(constraint_.poly);
}

ContractorResultQ RelationContractorQ::contract(ReasonedBoxQ& box) {
    // Univariate safeguard — multi-var requires corner enumeration which
    // explodes and is the linearizer's job, not ICP V1.
    if (vars_.size() != 1) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const std::string& var = vars_[0];
    auto riOpt = box.get(var);
    if (!riOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto degOpt = kernel_.degree(constraint_.poly, var);
    if (!degOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint_.poly, var);
    if (!coeffsOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const auto& coeffs = *coeffsOpt;
    const IntervalQ& xInterval = riOpt->interval;

    // Horner-style interval evaluation: Σ c_i · x^{deg-i}.
    // Reusing intervalQAdd/Mul/Pow — each is a sound over-approx.
    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (size_t i = 0; i < coeffs.size(); ++i) {
        const mpz_class& coeff = coeffs[i];
        if (coeff == 0) continue;
        size_t power = coeffs.size() - 1 - i;
        IntervalQ termInterval = intervalQPow(xInterval, static_cast<uint32_t>(power));
        if (coeff != 1) {
            mpq_class coeffQ(coeff);
            IntervalQ coeffInterval{coeffQ, coeffQ};
            termInterval = intervalQMul(coeffInterval, termInterval);
        }
        result = intervalQAdd(result, termInterval);
    }

    // Reasons combine the box's bound reasons with the constraint reason —
    // both are needed to make the conflict explanation sound.
    std::vector<SatLit> reasons = riOpt->reasons;
    reasons.push_back(constraint_.reason);

    if (isDefinitelyViolated(result, constraint_.rel)) {
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{reasons},
            {}
        };
    }

    return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
}

std::vector<std::string> RelationContractorQ::vars() const {
    return vars_;
}

SatLit RelationContractorQ::reason() const {
    return constraint_.reason;
}

bool RelationContractorQ::isDefinitelyViolated(const IntervalQ& polyInterval, Relation rel) const {
    // Over reals, intervals are closed [lo, hi] — strict relations need strict
    // sign separation, non-strict need non-strict separation. Each branch is the
    // contrapositive of "∃ value in interval satisfying rel"; if no value
    // satisfies, the asserted rel is impossible on this box → Conflict.
    switch (rel) {
        case Relation::Leq:
            // p ≤ 0 violated if every p in interval is > 0.
            return polyInterval.lo > 0;
        case Relation::Geq:
            // p ≥ 0 violated if every p in interval is < 0.
            return polyInterval.hi < 0;
        case Relation::Lt:
            // p < 0 violated if every p in interval is ≥ 0.
            return polyInterval.lo >= 0;
        case Relation::Gt:
            // p > 0 violated if every p in interval is ≤ 0.
            return polyInterval.hi <= 0;
        case Relation::Eq:
            // p = 0 violated if 0 ∉ interval.
            return !polyInterval.containsZero();
        case Relation::Neq:
            // p ≠ 0 violated if interval = {0}.
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false;
    }
}

} // namespace xolver
