#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * ArrayReadOverWrite — eager constant-index read-over-write store-chain folding.
 *
 * For a read `(select T c)` where the index `c` is an integer constant, walk the
 * store chain `T = (store (store ... base i1 v1 ...) ik vk)` once from the
 * outermost store inward, applying the read-over-write axiom on decidable
 * constant index comparisons:
 *
 *   select(store(a, i, v), j) = v            if i == j   (constants)
 *   select(store(a, i, v), j) = select(a, j) if i != j   (constants)
 *   select(const-array(v), j) = v
 *
 * The walk stops as soon as it meets a store whose index is *not* a constant
 * (it might alias `c`, so it cannot be skipped soundly) or a non-store base,
 * emitting a residual read on the (possibly shortened) chain for the array
 * theory to handle. This is exactly the array-simplifier fast path: it resolves
 * everything decidable by constant comparison and defers the rest, with no SAT
 * branching.
 *
 * EXACT (verdict-preserving) and GENERAL — it is the read-over-write axiom, not
 * a benchmark match. Bottom-up memoized DAG walk; new ExprIds via the IR's own
 * hash-cons; never mutates existing nodes. O(total store/select nodes).
 *
 * Motivation: deep constant-index store chains (SV-COMP CSeq concurrency
 * encodings, QF_ANIA `cs_*`) are resolved by the lazy array theory only via
 * per-store Row axioms, which is superlinear in chain length and never reaches
 * the bottom of a ~1800-deep chain. Folding them statically collapses the chain
 * to its resolved values, matching z3's sub-second time on the same files.
 */
class ArrayReadOverWrite {
public:
    explicit ArrayReadOverWrite(CoreIr& ir);

    bool run();          // returns didRewrite()
    void commit();
    bool didRewrite() const { return didRewrite_; }

private:
    ExprId rewriteRec(ExprId e);
    // Resolve `(select arr idx)` (children already rewritten). `orig` is the
    // original select ExprId, returned unchanged when nothing applies.
    ExprId resolveSelect(ExprId arr, ExprId idx, SortId sort, ExprId orig);
    bool intConstVal(ExprId e, mpz_class& out) const;
    bool isArraySort(SortId s) const;
    // Collect `(= arrvar T)` from top-level unconditional conjuncts (descending
    // only through And) into arrDef_. Such an equation holds in every model, so
    // `select(arrvar, c) == select(T, c)` is a sound rewrite — it lets the chain
    // walk thread through array equations (the SV-COMP CSeq encodings bind each
    // store result to a fresh array variable, breaking the syntactic chain).
    void buildArrayDefs();

    CoreIr& ir_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::unordered_set<ExprId> inProgress_;       // cycle guard for def-following
    std::unordered_map<ExprId, ExprId> arrDef_;   // array Variable -> its definition
    std::vector<std::pair<ScopeLevel, ExprId>> rewritten_;
    bool didRewrite_ = false;
};

} // namespace xolver
