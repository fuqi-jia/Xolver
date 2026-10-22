#pragma once

#include "ir/NativeTerms.h"
#include <unordered_map>
#include <optional>

namespace xolver {

/**
 * ModelValidator: independently verify that a model satisfies all assertions.
 *
 * Validates Boolean structure only. Unsupported terms are indeterminate and
 * cannot make validate()/eval() succeed (including under negation).
 */
class ModelValidator {
public:
    using BoolAssignment = std::unordered_map<ExprId, bool>;

    // Validate all assertions under the given boolean assignment.
    // Returns true iff every assertion evaluates to true.
    bool validate(const NativeTerms& ir, const BoolAssignment& assignment);

    // Check a single expression.
    bool eval(ExprId eid, const NativeTerms& ir, const BoolAssignment& assignment);

private:
    std::optional<bool> evalKnown(ExprId eid, const NativeTerms& ir,
                                 const BoolAssignment& assignment);
};

} // namespace xolver
