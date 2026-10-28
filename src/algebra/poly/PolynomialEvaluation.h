#pragma once

#include "ir/types.h"
#include <gmpxx.h>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>

namespace xolver {
class PolynomialKernel;

// An exact assignment snapshot shared by all polynomial checks of one model.
// The kernel must outlive this object. Values are copied; later changes to the
// caller's map cannot change an existing evaluation. Missing bindings yield no
// value. Create a new snapshot for a different candidate/query, never retain a
// mutable backend assignment as a cross-query cache.
class PolynomialEvaluation {
public:
    PolynomialEvaluation() = default;
    virtual ~PolynomialEvaluation() = default;
    PolynomialEvaluation(const PolynomialEvaluation&) = delete;
    PolynomialEvaluation& operator=(const PolynomialEvaluation&) = delete;

    virtual std::optional<mpq_class> evaluate(PolyId polynomial) const = 0;
    std::optional<mpz_class> evaluateInteger(PolyId polynomial) const;
    std::optional<int> sign(PolyId polynomial) const;
};

std::unique_ptr<PolynomialEvaluation> makePolynomialEvaluation(const PolynomialKernel& kernel,
    const std::unordered_map<std::string, mpz_class>& model);
std::unique_ptr<PolynomialEvaluation> makePolynomialEvaluation(const PolynomialKernel& kernel,
    const std::unordered_map<std::string, mpq_class>& model);

} // namespace xolver
