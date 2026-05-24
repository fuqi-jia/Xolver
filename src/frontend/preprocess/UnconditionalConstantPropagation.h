#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>

namespace nlcolver {

/**
 * UnconditionalConstantPropagation (Capability 8a of the
 * close-all-known-fails plan).
 *
 * Frontend, syntactic-only pass.
 *
 * Two phases per run():
 *   1. Collection. Walk every top-level assertion. If the assertion is
 *      a Kind::And, flatten the top-level conjunction; otherwise treat
 *      the assertion itself as a single unconditional conjunct.
 *      Among those unconditional conjuncts, collect every
 *      (= var ConstNumeric) where var is a Kind::Variable and the RHS
 *      is a numeric literal (ConstInt, or ConstReal whose rational
 *      string is an integer/rational literal). Build a map
 *      VarId -> mpq_class.
 *   2. Substitution. Once a variable is bound to an unconditional
 *      constant, that equality holds in every model of the formula,
 *      so we substitute occurrences of the variable by the constant
 *      *globally*, including occurrences nested under or / =>  / not
 *      / ite / mod / div / to_real / to_int / arithmetic ops.
 *
 * On contradictory bindings (e.g. (= x 2) AND (= x 3) both
 * unconditionally asserted), `hadContradiction()` returns true and the
 * caller can short-circuit to UNSAT.
 *
 * The pass never mutates existing CoreExpr nodes; it builds fresh
 * ExprIds and produces a new assertion list via `commit()`.
 */
class UnconditionalConstantPropagation {
public:
    explicit UnconditionalConstantPropagation(CoreIr& ir);

    // Returns false only on fatal IR error. Run-not-found is reported
    // via hadContradiction(); the caller decides whether to short-
    // circuit (Solver returns Unsat) or continue.
    bool run();

    bool hadContradiction() const { return contradiction_; }

    // Rewrite assertions per the substitution map, replacing existing
    // assertion list. Safe to call only after run() returned true and
    // hadContradiction() is false.
    void commit();

    // Read-only access to the collected substitution map, for diagnostic
    // logging / unit testing.
    const std::unordered_map<std::string, mpq_class>& fixedConstMap() const {
        return fixedConstMap_;
    }

private:
    // Collection helpers.
    void collectFromAssertion(ExprId assertion);
    void collectFromConjunct(ExprId conjunct);
    bool tryRecordBinding(const std::string& varName, const mpq_class& value);

    // Phase-2 helpers: assertion-level rewriting preserves the
    // source-of-binding equality atoms (so downstream theories still
    // see `x = c` as an active literal); only the other conjuncts are
    // substituted globally.
    ExprId substituteAssertion(ExprId assertion);
    bool isSourceOfBinding(ExprId conjunct) const;

    // Substitution helper. Memoized over (ExprId) -> (ExprId).
    ExprId substituteRec(ExprId e);

    // After substitution, fold any newly-constant arithmetic / boolean
    // sub-expression. Required because downstream Atomizer registers
    // (Tautology / Conflict)-status arithmetic atoms as no-ops, which
    // leaves the corresponding SAT variable free and breaks soundness
    // when the atom would have been logically determined.
    ExprId constantFoldRec(ExprId e);
    // Try to fold a single node; returns the folded ExprId or e if no
    // fold applied.
    ExprId tryFoldArithmetic(ExprId e);
    ExprId tryFoldRelation(ExprId e);
    ExprId tryFoldBoolean(ExprId e);

    // Constant extraction (delegates to the IR's payload variants).
    std::optional<mpq_class> tryAsConstNumeric(ExprId e) const;
    std::optional<bool> tryAsConstBool(ExprId e) const;

    // Build a fresh ConstReal or ConstInt expression at the given sort.
    ExprId materializeConstant(const mpq_class& value, SortId sort);
    ExprId mkBool(bool value);

    CoreIr& ir_;
    SortId boolSortId_;
    SortId intSortId_;
    SortId realSortId_;

    std::unordered_map<std::string, mpq_class> fixedConstMap_;
    bool contradiction_ = false;

    std::unordered_map<ExprId, ExprId> substMemo_;
    std::unordered_map<ExprId, ExprId> foldMemo_;
    // (sort, canonical-rational-string) -> ExprId. Required so that two
    // substitutions producing the "same" constant value share the
    // same ExprId; the relation/identity folds in Capability 8a rely
    // on ExprId equality for sub-expressions like `(f 2)`, so without
    // sharing the fold misses `(distinct (f 2) (f 2)) -> false` when
    // one `2` came from substitution and the other came from the
    // original literal.
    std::unordered_map<std::string, ExprId> constCache_;
    std::unordered_map<std::string, ExprId> boolConstCache_;
    std::vector<std::pair<ScopeLevel, ExprId>> rewrittenAssertions_;
};

} // namespace nlcolver
