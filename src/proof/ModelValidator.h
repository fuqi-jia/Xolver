#pragma once

#include "expr/ir.h"
#include <unordered_map>

namespace zolver {

/**
 * ModelValidator: independently verify that a model satisfies all assertions.
 *
 * Stage A: validates boolean structure only.
 * Future: exact arithmetic validation, BV bit-precise, algebraic number sign eval.
 */
class ModelValidator {
public:
    using BoolAssignment = std::unordered_map<ExprId, bool>;

    // Validate all assertions under the given boolean assignment.
    // Returns true iff every assertion evaluates to true.
    bool validate(const CoreIr& ir, const BoolAssignment& assignment);

    // Check a single expression.
    bool eval(ExprId eid, const CoreIr& ir, const BoolAssignment& assignment);
};

} // namespace zolver
