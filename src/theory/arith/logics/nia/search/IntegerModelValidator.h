#pragma once

#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include <unordered_map>
#include <vector>

namespace xolver {

using IntegerModel = std::unordered_map<std::string, mpz_class>;

/**
 * IntegerModelValidator: exact integer validation for SAT results.
 *
 * Uses kernel_.evalInteger() to evaluate each normalized constraint at the
 * proposed integer model.
 */
class IntegerModelValidator {
public:
    enum class Result { Valid, Violated, Indeterminate };

    explicit IntegerModelValidator(PolynomialKernel& kernel);

    Result validate(const IntegerModel& model,
                    const std::vector<NormalizedNiaConstraint>& constraints) const;

private:
    PolynomialKernel& kernel_;

    bool relationHolds(const mpz_class& val, Relation rel) const;
};

} // namespace xolver
