#pragma once

#include "ir/types.h"
#include "ir/NativeTerms.h"
#include "contracts/LinearFormKey.h"
#include <gmpxx.h>
#include <string>
#include <vector>
#include <unordered_map>

namespace xolver {

// ============================================================================
// Extract a linear expression from TermExpr.
// Returns true iff the expression is linear.
// Output: coeffs[var] += coeff, constant += constant_term.
// ============================================================================
bool extractLinearExpr(ExprId eid, const NativeTerms& ir,
                       std::unordered_map<std::string, mpq_class>& coeffs,
                       mpq_class& constant,
                       const mpq_class& mul = mpq_class(1));

// ============================================================================
// Extract a linear constraint from TermExpr (Eq, Lt, Leq, Gt, Geq, Distinct).
// Returns true iff the expression is a linear constraint.
// Output: coeffs, rhs (such that sum(coeff_i * var_i) = rhs at equality)
// ============================================================================
bool extractLinearConstraint(ExprId eid, const NativeTerms& ir,
                              std::unordered_map<std::string, mpq_class>& coeffs,
                              mpq_class& rhs, Relation& rel);

// ============================================================================
// Negate a relation.
// ============================================================================
Relation negateRelation(Relation r);

} // namespace xolver
