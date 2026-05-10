#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include <gmpxx.h>
#include <string>
#include <vector>
#include <unordered_map>

namespace nlcolver {

// ============================================================================
// LinearFormKey: canonical representation of a linear expression's LHS.
// Contains only variable terms (no constant). Sorted by var name for hashing.
// ============================================================================
struct LinearFormKey {
    std::vector<std::pair<std::string, mpq_class>> terms;  // sorted by var name

    bool operator==(const LinearFormKey& o) const {
        if (terms.size() != o.terms.size()) return false;
        for (size_t i = 0; i < terms.size(); ++i) {
            if (terms[i].first != o.terms[i].first) return false;
            if (terms[i].second != o.terms[i].second) return false;
        }
        return true;
    }
};

struct LinearFormKeyHash {
    std::size_t operator()(const LinearFormKey& f) const {
        std::size_t h = 0;
        for (const auto& t : f.terms) {
            h ^= std::hash<std::string>{}(t.first) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<std::string>{}(t.second.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

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

} // namespace nlcolver
