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

bool IntegerModelValidator::validate(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {

    for (const auto& c : constraints) {
        auto valOpt = kernel_.evalInteger(c.poly, model);
        if (!valOpt) {
            // Cannot evaluate → cannot validate
            return false;
        }
        if (!relationHolds(*valOpt, c.rel)) {
            return false;
        }
    }
    return true;
}

} // namespace nlcolver
