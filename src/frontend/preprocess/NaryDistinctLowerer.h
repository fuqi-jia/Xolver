#pragma once

#include "expr/ir.h"
#include <unordered_map>

namespace xolver {

/**
 * NaryDistinctLowerer: lowers n-ary (n>2) Kind::Distinct into pairwise binary distinct.
 *
 * Invariants:
 *   - Pure IR-to-IR, no SAT/theory interaction.
 *   - distinct(c0,c1,...,cn-1) -> and( distinct(c0,c1), distinct(c0,c2), ..., distinct(c_{n-2},c_{n-1}) )
 *   - n=0/1: lower to true (should not occur in valid SMT-LIB)
 *   - DAG sharing via memo table.
 */
class NaryDistinctLowerer {
public:
    explicit NaryDistinctLowerer(CoreIr& ir);

    // Run lowering phase. Returns true if all n-ary distinct were lowered.
    bool run();

    // Commit lowered assertions back to CoreIr.
    void commit();

private:
    ExprId lowerRec(ExprId e);
    ExprId lowerDistinct(const std::vector<ExprId>& children);
    ExprId mkDistinct(ExprId a, ExprId b);
    ExprId mkAnd(ExprId a, ExprId b);
    ExprId mkTrue();

    CoreIr& ir_;
    SortId boolSortId_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<std::pair<ScopeLevel, ExprId>> loweredAssertions_;
};

} // namespace xolver
