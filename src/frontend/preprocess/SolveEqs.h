#pragma once

#include "ir/NativeTerms.h"
#include "frontend/preprocess/ModelConverter.h"
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * SolveEqs — reconstructable definition elimination (↔SAT, P1).
 *
 * Eliminates a user variable `x` defined by an unconditional top-level equality
 * conjunct `(= x t)` (or `(= t x)`) where `x` is a bare numeric Variable that
 * does not occur in `t`, and `t` is a *linear, reconstructable* term (only
 * Add/Sub/Neg/Mul-by-constant/ToReal over variables and constants — no
 * div/mod/pow/UF/ITE/array). Substitutes `x ↦ t` globally, drops the defining
 * equality, and registers `(x, t)` with a ModelConverter so the eliminated
 * value is rebuilt on the final model (replay correctness).
 *
 * This is equisatisfiable, not equivalent: the variable is gone from the
 * formula, so the pass MUST be paired with the ModelConverter and gated off
 * under incremental push/pop. One elimination at a time + global re-substitution
 * (so a later equality whose term referenced `x` is solved over the remaining
 * variables); reverse-order replay in the converter resolves dependencies.
 *
 * Linear is the default policy. PolynomialInLinearPositions also accepts
 * products in defining terms, provided the eliminated variable has only linear
 * uses. It preserves polynomial degree and uses exact rational model replay.
 */
class SolveEqs {
public:
    enum class DefinitionPolicy { Linear, PolynomialInLinearPositions };
    SolveEqs(NativeTerms& ir, ModelConverter& mc,
             DefinitionPolicy policy = DefinitionPolicy::Linear);

    // Eliminate as many variables as possible (fixpoint, bounded). Returns true
    // if any variable was eliminated.
    bool run();

    // Replace the IR assertion list with the substituted conjuncts.
    void commit();

    size_t eliminatedCount() const { return eliminated_; }

private:
    // Populate unsafeVars_ with every variable occurring under a UFApply /
    // Select / Store (an uninterpreted-function/array argument). Eliminating
    // such a variable severs a Nelson-Oppen shared term and is unsound in
    // combination logics (false-SAT). Computed once at the start of run():
    // eliminating a non-UF variable only moves its term into non-UF positions,
    // so the set remains valid across eliminations.
    void computeUnsafeVars();

    // Is `e` a bare Variable of Int/Real sort? Returns its name if so.
    std::optional<std::string> asNumericVar(ExprId e) const;
    // Does Variable named `name` occur anywhere in `e`?
    bool occurs(const std::string& name, ExprId e) const;
    // Is `e` a linear, reconstructable term (see class doc)?
    bool isReconstructable(ExprId e, bool polynomial) const;
    bool admissibleDefinition(const std::string& name, ExprId e);
    bool hasOnlyLinearUses(const std::string& name);
    // Substitute Variable named `name` by `replacement` throughout `e` (memoized).
    ExprId substitute(ExprId e, const std::string& name, ExprId replacement);

    NativeTerms& ir_;
    ModelConverter& mc_;
    DefinitionPolicy policy_;
    SortId boolSortId_;
    SortId intSortId_;
    SortId realSortId_;

    std::vector<std::pair<ScopeLevel, ExprId>> conjuncts_;
    std::unordered_set<std::string> unsafeVars_;     // occur under UF/array app
    std::unordered_map<ExprId, ExprId> substMemo_;  // cleared per substitution
    size_t eliminated_ = 0;
    bool didRun_ = false;

    // Substitution-work guard (see run()). Counts node-visits across all
    // substitute() calls; when it exceeds workBudget_ the elimination loop stops
    // (partial pass is sound). Bounds the O(eliminations × formula-size) cost
    // that otherwise turns large chained-equality UNSATs (SMPT/nec) into
    // timeouts. Default tuned so small formulas (convert) finish; env-overridable
    // via XOLVER_PP_SOLVE_EQS_BUDGET.
    uint64_t substWork_ = 0;
    uint64_t workBudget_ = 40'000'000;

};

} // namespace xolver
