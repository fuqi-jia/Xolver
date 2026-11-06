#pragma once

#include "ir/types.h"
#include "ir/NativeTerms.h"
#include "contracts/LinearFormKey.h"
#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <optional>
#include <span>
#include <string>
#include <utility>
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
                       const mpq_class& mul = mpq_class(1), WorkBudget* budget = nullptr);

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

// A representative-model radius for integer difference predicates, allowing a
// consistent sign change of each variable and arbitrary nonzero rational scales.
// Supply EVERY affine atom as (lhs, rhs); any comparison and Boolean combination
// is allowed. Unsupported forms return nullopt. This is a satisfiability cover,
// NOT an entailed bound on every model; do not export it as a theory lemma.
std::optional<mpz_class> integerDifferenceCoverRadius(
    std::span<const std::pair<LinearFormKey, mpq_class>> forms);

} // namespace xolver
