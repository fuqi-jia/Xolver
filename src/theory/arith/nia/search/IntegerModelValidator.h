#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include <unordered_map>
#include <vector>

namespace nlcolver {

using IntegerModel = std::unordered_map<std::string, mpz_class>;

/**
 * IntegerModelValidator: exact integer validation for SAT results.
 *
 * Uses kernel_.evalInteger() to evaluate each normalized constraint at the
 * proposed integer model. Returns true iff all constraints are satisfied.
 */
class IntegerModelValidator {
public:
    explicit IntegerModelValidator(PolynomialKernel& kernel);

    bool validate(const IntegerModel& model,
                  const std::vector<NormalizedNiaConstraint>& constraints) const;

private:
    PolynomialKernel& kernel_;

    bool relationHolds(const mpz_class& val, Relation rel) const;
};

} // namespace nlcolver
