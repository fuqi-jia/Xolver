#include "theory/arith/nia/search/IntegerModelValidator.h"

namespace nlcolver {

IntegerModelValidator::IntegerModelValidator(PolynomialKernel& kernel) : kernel_(kernel) {}

bool IntegerModelValidator::relationHolds(const mpz_class& val, Relation rel) const {
    switch (rel) {
        case Relation::Eq:  return val == 0;
        case Relation::Neq: return val != 0;
        case Relation::Lt:  return val <  0;
        case Relation::Leq: return val <= 0;
        case Relation::Gt:  return val >  0;
        case Relation::Geq: return val >= 0;
    }
    return false;
}

IntegerModelValidator::Result IntegerModelValidator::validate(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {

    bool anyIndeterminate = false;
    for (const auto& c : constraints) {
        auto valOpt = kernel_.evalInteger(c.poly, model);
        if (!valOpt) {
            // Distinguish "missing variable in model" (indeterminate) from
            // "evaluation produced non-integer" (also indeterminate).
            // The caller must decide whether to trust this model.
            anyIndeterminate = true;
            continue;
        }
        if (!relationHolds(*valOpt, c.rel)) {
            return Result::Violated;
        }
    }
    if (anyIndeterminate) {
        return Result::Indeterminate;
    }
    return Result::Valid;
}

} // namespace nlcolver
