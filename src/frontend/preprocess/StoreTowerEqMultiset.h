#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * StoreTowerEqMultiset — reduce increment-store-tower array equality to an
 * index-multiset equality over arithmetic.
 *
 * Pattern (PLONK grand-product soundness benchmarks, Ozdemir 2021, QF_ANIA):
 *   an N-fold tower  store(store(..store(B, i1, B[i1]+1).., iN, prev[iN]+1))
 *   where every stored value is `(+ (select <running array> <idx>) 1)`, i.e.
 *   each store increments the RUNNING array at its index by 1.
 *
 * For such a tower over base B,  tower[x] = B[x] + count(x in {i1..iN})  (the
 * running-read makes same-index stores accumulate). Hence two towers over the
 * SAME base are equal as arrays IFF their index MULTISETS are equal:
 *
 *   store-tower(B, [i1..iN]) = store-tower(B, [j1..jN])
 *      <=>   multiset{i1..iN} = multiset{j1..jN}
 *      <=>   OR over permutations sigma of  AND_k ( i_k = j_sigma(k) )
 *
 * This is EXACT (the base B cancels; the only constraint is matching counts),
 * so SAT and UNSAT are both preserved. It eliminates the arrays entirely,
 * leaving a pure arithmetic constraint the NIA solver can search — the
 * GrandProduct models otherwise time out because the array store-tower
 * equality is never reduced and the `beta` offsets are unbounded.
 *
 * GENERAL: matches the structural increment-tower shape only (a non-increment
 * store equality, e.g. `store(B,i,v) = store(B,j,w)`, fails the value check and
 * is left untouched). No example-specific constants.
 *
 * Memoized DAG walk; new ExprIds via a local hash-cons; never mutates.
 */
class StoreTowerEqMultiset {
public:
    explicit StoreTowerEqMultiset(CoreIr& ir);

    bool run();
    void commit();
    bool didRewrite() const { return didRewrite_; }

private:
    ExprId rewriteRec(ExprId e);

    // If `T` is an increment-store-tower, set base + the index list (bottom-up)
    // and return true. A bare (non-Store) array is a valid base with no indices.
    bool detectTower(ExprId T, ExprId& base, std::vector<ExprId>& indices) const;

    bool isIntConstEq(ExprId e, int64_t v) const;

    // OR over permutations of AND_k (a[k] == b[perm[k]]), bool-sorted.
    ExprId buildMultisetEq(const std::vector<ExprId>& a,
                           const std::vector<ExprId>& b, SortId boolSort);

    ExprId cons(CoreExpr e);

    CoreIr& ir_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::unordered_map<std::string, ExprId> consCache_;
    std::vector<std::pair<ScopeLevel, ExprId>> rewritten_;
    bool didRewrite_ = false;

    // Safety cap: N! disjuncts; refuse towers taller than this so the encoding
    // can't blow up (GrandProduct uses N=3..5; 7! = 5040 is the ceiling).
    static constexpr size_t kMaxTowerHeight = 7;
};

} // namespace xolver
