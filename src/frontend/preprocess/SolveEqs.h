#pragma once

#include "expr/ir.h"
#include "frontend/preprocess/ModelConverter.h"
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * SolveEqs — solve-equalities / linear variable elimination (↔SAT, P1).
 *
 * Eliminates a user variable `x` defined by an unconditional top-level equality
 * conjunct `(= x t)` (or `(= t x)`) where `x` is a bare numeric Variable that
 * does not occur in `t`, and `t` is a *linear, reconstructable* term (only
 * Add/Sub/Neg/Mul-by-constant/ToReal/ToInt over variables and constants — no
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
 * Linearity + reconstructability guarantee: every SAT model is reconstructable
 * (evalRational succeeds), and no nonlinearity is introduced into the formula.
 */
class SolveEqs {
public:
    SolveEqs(CoreIr& ir, ModelConverter& mc);

    // Eliminate as many variables as possible (fixpoint, bounded). Returns true
    // if any variable was eliminated.
    bool run();

    // Enable general linear ±1-pivot elimination (XOLVER_PP_SOLVE_EQS_GAUSS).
    // When on, the pass additionally solves a general linear equality
    // Σ aᵢ·xᵢ = c for any variable xⱼ whose coefficient is ±1 (so the
    // reconstruction xⱼ = ∓(Σᵢ≠ⱼ aᵢ·xᵢ − c) is exact and integer-preserving —
    // no division introduced). This unlocks the Farkas-style `expr = expr`
    // equalities that the bare-var path (`x = t`) cannot touch. Off by default;
    // independently gated for ablation.
    void setGeneralLinear(bool b) { generalLinear_ = b; }

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
    bool isLinearReconstructable(ExprId e) const;
    // Substitute Variable named `name` by `replacement` throughout `e` (memoized).
    ExprId substitute(ExprId e, const std::string& name, ExprId replacement);

    // General ±1-pivot elimination: if conjunct `idx` is a linear equality with
    // a variable whose coefficient is ±1 (and that variable is safe to
    // eliminate), isolate it, build the exact linear replacement, substitute it
    // out, drop the equality, and register the elimination. Returns true on
    // success (caller restarts the scan). Only fires when generalLinear_ is set.
    bool tryGeneralEliminate(size_t idx);

    CoreIr& ir_;
    ModelConverter& mc_;
    SortId boolSortId_;
    SortId intSortId_;
    SortId realSortId_;

    std::vector<std::pair<ScopeLevel, ExprId>> conjuncts_;
    std::unordered_set<std::string> unsafeVars_;     // occur under UF/array app
    std::unordered_map<ExprId, ExprId> substMemo_;  // cleared per substitution
    size_t eliminated_ = 0;
    bool didRun_ = false;
    bool generalLinear_ = false;     // XOLVER_PP_SOLVE_EQS_GAUSS

    // Substitution-work guard (see run()). Counts node-visits across all
    // substitute() calls; when it exceeds workBudget_ the elimination loop stops
    // (partial pass is sound). Bounds the O(eliminations × formula-size) cost
    // that otherwise turns large chained-equality UNSATs (SMPT/nec) into
    // timeouts. Default tuned so small formulas (convert) finish; env-overridable
    // via XOLVER_PP_SOLVE_EQS_BUDGET.
    uint64_t substWork_ = 0;
    uint64_t workBudget_ = 40'000'000;

    // Densification guard for general ±1-pivot elimination (see run()). When the
    // live formula DAG grows past growthCap_× its initial size, general
    // elimination is fanning out hub variables (UNSAT-harmful) and is disabled
    // for the rest of the pass. growthCap_ tuned so SAT-helpful elimination
    // (which shrinks: ratio<1) never trips and Petri-net densification (ratio
    // ~1.9+) does; env-overridable via XOLVER_PP_SOLVE_EQS_GROWTH_CAP.
    bool gaussDensifyAbort_ = false;
    double growthCap_ = 1.30;
    static constexpr size_t kGrowthCheckEvery_ = 4;
};

} // namespace xolver
