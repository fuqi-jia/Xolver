#pragma once

#include "xolver/Term.h"
#include <cstdint>
#include <vector>

namespace xolver {

/**
 * One observable atom exposed to a user Propagator: a SAT variable and the term
 * it encodes. `isTheory` distinguishes a theory atom (e.g. `x <= 5`, `f(a)=b`)
 * from a pure boolean-structure variable.
 */
struct ObservedAtom {
    uint32_t var = 0;     // CaDiCaL SAT variable (>= 1)
    Term term;            // the atom expression
    bool isTheory = false;
};

/// Effort of a theory consistency check: Standard fires during propagation on a
/// partial assignment; Full fires on a complete boolean model.
enum class CheckEffort { Standard, Full };

/// Outcome of a theory consistency check.
enum class CheckOutcome { Consistent, Conflict, Lemma, Unknown };

/**
 * User Propagator — a "one-step" control surface over the CDCL(T) search,
 * exposing BOTH levels of the loop:
 *
 *   * SAT level  (IPASIR-UP style): literal assignments, decision levels,
 *     backtracks, and decision steering; and
 *   * SMT level  (theory): a theory atom being fixed, the theory consistency
 *     check (with its effort and outcome), the conflicts / lemmas / propagations
 *     the theory generates, the complete-model final check, and the ability to
 *     GENERATE theory lemmas of your own.
 *
 * Subclass it, override the hooks you care about (all have no-op defaults), and
 * register with `Solver::setPropagator(&p)` BEFORE `checkSat()`. The propagator
 * must outlive the checkSat() call.
 *
 * SOUNDNESS. The OBSERVE hooks and decision steering are sound by construction
 * (observation cannot change a verdict; steering only reorders the search — a
 * wrong guess is backtracked). The one exception is `generateLemmas()`: an
 * invalid lemma can make a verdict wrong, so it is opt-in and its contract is
 * spelled out below. When no propagator is registered every forward is a guarded
 * no-op and the search is byte-identical to the default path.
 */
class Propagator {
public:
    virtual ~Propagator() = default;

    // ---- setup -----------------------------------------------------------
    /// Called once, on the first callback of a solve, with every observable
    /// atom (var <-> term). Build your own maps here for steering / read-back.
    virtual void onSetup(const std::vector<ObservedAtom>& atoms) { (void)atoms; }

    // ---- SAT level -------------------------------------------------------
    /// `var` was assigned `value` (`isDecision`: a branch vs. an implication).
    virtual void onAssignment(uint32_t var, bool value, bool isDecision) {
        (void)var; (void)value; (void)isDecision;
    }
    /// A fresh decision level was opened.
    virtual void onNewDecisionLevel() {}
    /// The search backtracked to decision level `level`.
    virtual void onBacktrack(uint32_t level) { (void)level; }
    /// Pick the next decision: a signed literal (`var` true / `-var` false), or
    /// 0 to defer to Xolver. Must name an UNASSIGNED variable; an already-fixed
    /// pick is safely ignored. Pure heuristic.
    virtual int decide() { return 0; }

    // ---- SMT / theory level ----------------------------------------------
    /// A theory atom `atom` (SAT var `var`) was fixed to `value`.
    virtual void onFixed(uint32_t var, bool value, Term atom) {
        (void)var; (void)value; (void)atom;
    }
    /// The theory consistency check ran at `effort` and returned `outcome`.
    virtual void onTheoryCheck(CheckEffort effort, CheckOutcome outcome) {
        (void)effort; (void)outcome;
    }
    /// The theory produced a conflict clause (literals as signed SAT vars).
    virtual void onConflict(const std::vector<int>& clause) { (void)clause; }
    /// The theory produced a lemma clause (literals as signed SAT vars).
    virtual void onLemma(const std::vector<int>& clause) { (void)clause; }
    /// The theory entailed/propagated a literal via a reason clause.
    virtual void onPropagate(const std::vector<int>& clause) { (void)clause; }
    /// A complete, theory-consistent model was found (about to report `sat`).
    virtual void onFinalCheck() {}

    // ---- generation (ADVANCED, soundness-sensitive) ----------------------
    /// Return theory lemmas (each a clause of signed SAT vars) to add at the
    /// final check. A clause the current model FALSIFIES rejects that model and
    /// the search continues; a clause that does not exclude the model is ignored
    /// (so the search always makes progress and terminates). An INVALID clause
    /// can make the verdict wrong — return ONLY valid theory consequences. The
    /// signed vars should name observed atoms (see onSetup). Default: none.
    virtual std::vector<std::vector<int>> generateLemmas() { return {}; }
};

} // namespace xolver
