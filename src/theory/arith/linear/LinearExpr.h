#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "theory/core/LinearFormKey.h"
#include <gmpxx.h>
#include <string>
#include <vector>
#include <unordered_map>

namespace zolver {

// ============================================================================
// Extract a linear expression from CoreExpr.
// Returns true iff the expression is linear.
// Output: coeffs[var] += coeff, constant += constant_term.
// ============================================================================
bool extractLinearExpr(ExprId eid, const CoreIr& ir,
                       std::unordered_map<std::string, mpq_class>& coeffs,
                       mpq_class& constant,
                       const mpq_class& mul = mpq_class(1));

// ============================================================================
// Extract a linear constraint from CoreExpr (Eq, Lt, Leq, Gt, Geq, Distinct).
// Returns true iff the expression is a linear constraint.
// Output: coeffs, rhs (such that sum(coeff_i * var_i) = rhs at equality)
// ============================================================================
bool extractLinearConstraint(ExprId eid, const CoreIr& ir,
                              std::unordered_map<std::string, mpq_class>& coeffs,
                              mpq_class& rhs, Relation& rel);

// ============================================================================
// Negate a relation.
// ============================================================================
Relation negateRelation(Relation r);

} // namespace zolver
