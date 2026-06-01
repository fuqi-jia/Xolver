#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <optional>
#include <unordered_map>

namespace xolver {

// Phase L1 step 2 — persistent state carried across cb_check calls.
// The original NiaLocalSearch ran a fresh restart on every call, which
// wasted any progress accumulated by the previous walk-sat trajectory.
// Yices2LS-style integration keeps a per-solver-instance context that
// the next call resumes from.
//
// Soundness contract:
//   - The context state NEVER influences a verdict. The caller (NiaSolver)
//     validates any Sat with IntegerModelValidator on the original
//     constraints. A bad context only wastes search effort, never produces
//     a wrong answer.
//   - On any structural change (assertion stack shrink, constraint set
//     change, kernel reset), the context is invalidated and reset.
//   - Signature mismatch ⇒ partial reinit (keep PAWS weights, drop
//     assignment); active-set signature changed but the formula's overall
//     hardness profile probably hasn't.
struct NiaLsContext {
    // Best assignment seen so far across calls (empty until first SAT
    // attempt). Carried so a subsequent call can warm-start from it.
    IntegerModel bestAssignment;
    mpz_class bestCost = 0;     // linear LS-IA distance at bestAssignment
    bool bestValid = false;     // false until at least one valid eval

    // Most-recent in-progress assignment (may differ from best if the
    // current trajectory has worsened beyond the best). Empty when no
    // walk has run yet.
    IntegerModel currentAssignment;

    // PAWS clause weights keyed by stable constraint hash. Persists
    // across calls so hard clauses stay hard.
    std::unordered_map<uint64_t, mpz_class> clauseWeight;

    // Variable activity boost: how many times each var participated in
    // an improving move recently. Read by NiaSolver to bias decision
    // priority (Phase L1 step 3 hooks this).
    std::unordered_map<std::string, uint64_t> varActivity;

    // Signature of the active constraint set on the call that last
    // populated this context. Used to detect "structurally same" calls.
    uint64_t lastSignature = 0;

    // Reset the context to the empty state (used on assertion backtrack
    // / solver reset / structural change). Sound at every point: a fresh
    // context just means the next call starts cold.
    void reset() {
        bestAssignment.clear();
        bestCost = 0;
        bestValid = false;
        currentAssignment.clear();
        clauseWeight.clear();
        varActivity.clear();
        lastSignature = 0;
    }
};

/**
 * NiaLocalSearch: heuristic SAT finder for NIA.
 *
 * Phase NIA-Core: skeleton only. Tries a few candidate assignments.
 */
class NiaLocalSearch {
public:
    explicit NiaLocalSearch(PolynomialKernel& kernel);

    std::optional<IntegerModel> tryFindModel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains);

    // Per-call wall-clock budget in ms; <= 0 means unlimited. The search is a
    // heuristic candidate finder, so giving up early just returns nullopt
    // (no model this call) -- always sound. Default from XOLVER_NIA_LS_BUDGET_MS.
    void setBudgetMs(long ms) { budgetMs_ = ms; }

    // Cumulative per-solve budget: the SAT core triggers a full-effort theory
    // check on every complete assignment (hundreds on branchy QF_NIA), each
    // re-running this search from scratch -- futile on UNSAT and ~10s in total.
    // Once cumulative search time exceeds this, the search is skipped entirely
    // (returns nullopt) so the cheap reasoning stages get the time. Sound
    // (candidate-only). Reset per solve. Default from XOLVER_NIA_LS_TOTAL_MS.
    void resetBudget() { cumulativeMs_ = 0; }

    // Enable the WalkSAT / accelerated-hill-climb search (XOLVER_NIA_LOCALSEARCH,
    // default-OFF). Settable for tests.
    void setEnhanced(bool e) { enhanced_ = e; }
    // Phase L1: enable the LS-IA + Yices2LS-style enhancements on top of the
    // base walkSat — incremental per-clause violation tracking, PAWS clause
    // weights, accelerated hill-climb with adaptive step (acc=1.2).
    // Default-OFF (XOLVER_NIA_LS_TWO_LEVEL=1). Pure perf / SAT-finder
    // improvement; soundness invariants unchanged (candidate-only,
    // validator-gated, never returns UNSAT).
    void setTwoLevel(bool e) { twoLevel_ = e; }
    // Phase L1 step 2: enable persistent NiaLsContext warm-start across
    // cb_check calls. Default-OFF (XOLVER_NIA_LS_WARM_START=1). The
    // context survives across tryFindModel calls; structural change /
    // backtrack invalidates it. SOUNDNESS: context state is heuristic
    // bias only and never influences a verdict (every Sat is still
    // validator-gated; every UNSAT-claim is impossible from LS).
    void setWarmStart(bool e) { warmStart_ = e; }
    // Phase L1 step P2 — multi-scale step (XOLVER_NIA_LS_MULTI_SCALE=1,
    // default-OFF). Replaces the geometric (6/5)^k series around the
    // discrete-Newton step with doubling (±1, ±2, ±4, ±8, ±16, ...) plus
    // √|val| target candidates for x²=N patterns. Better coverage on
    // bilinear/quadratic systems without changing soundness.
    void setMultiScale(bool e) { multiScale_ = e; }
    // Phase L1 P3 — degree ≤ 2 critical move (XOLVER_NIA_LS_QUAD_CRITICAL=1,
    // default-OFF). For each falsified constraint, fit a quadratic model
    // q(t) = at² + bt + c via three probes (orig, orig+1, orig+2), solve
    // for integer-rounded roots, and add them to the move target set.
    // LS-IA paper: degree ≥ 3 is skipped intentionally for performance.
    void setQuadCritical(bool e) { quadCritical_ = e; }
    // Phase L1 P4 — feasible-set jump (XOLVER_NIA_LS_FS_JUMP=1,
    // default-OFF). For each variable in a falsified atom, augment the
    // move target set with the DomainStore's boundary/midpoint values
    // and finite-set elements. Yices2LS-style: "lazy cell jumps" via
    // the maintained feasibility intervals — no root isolation, sound
    // by construction.
    void setFsJump(bool e) { fsJump_ = e; }
    // Phase L1 P5 — diversified restart probes
    // (XOLVER_NIA_LS_DIVERSE_INIT=1, default-OFF). Rotate initial
    // assignments across restarts: zeros, boundaries, ±10/±100/±500
    // anchors, small-random. SAT14 z3 models show many cases satisfy at
    // anchor values 100-300 outside the multi-scale doubling's grasp
    // from a zero start. Probing those anchors at restart time gives the
    // LS a credible starting trajectory.
    void setDiverseInit(bool e) { diverseInit_ = e; }
    // Phase L1 P5 — bilinear pair move
    // (XOLVER_NIA_LS_BILINEAR_PAIR=1, default-OFF). When a falsified
    // atom's polynomial contains a `(* x y)` product, propose joint
    // (x, y) updates that bring the product close to its target. Targets
    // integer factor pairs (1×n, 2×n/2, …) of the desired product value.
    // Single-variable Newton is misleading on bilinear systems; joint
    // updates respect the bilinear interaction directly.
    void setBilinearPair(bool e) { bilinearPair_ = e; }
    // Phase B (VeryMax PRIMARY, master 2026-06-01) — bilinear-substitution
    // move (XOLVER_NIA_LS_BILINEAR_SUBST=1, default-OFF). Generalises
    // bilinear-pair from product-only targets to ANY 2-var atom: for each
    // (x, y) appearing together in some monomial, fix one at its current
    // value and treat the atom as a univariate polynomial in the other,
    // then propose the integer root(s). Handles linear (closed-form
    // -b/a) and quadratic (discriminant integer-root) residuals; degree
    // >=3 in the solve-variable is skipped. The new candidate enters the
    // same bestCost selection as discrete-Newton / multi-scale /
    // quad-critical, so soundness is unchanged.
    void setBilinearSubst(bool e) { bilinearSubst_ = e; }
    // LS-VM1 (master 2026-06-02 8h directive). Pre-pin variables whose
    // values are completely determined by an Eq atom of the form
    // c*x + k = 0 with c|k (single-var linear equality, integer root).
    // The LS walk then SKIPS these variables (no perturbation, no
    // contribution to varToClauses move selection) and pre-loads their
    // pinned value into the starting assignment. CInteger has explicit
    // Farkas equality chains in every case; SAT14 + ITS have these in
    // their initial-state defs. Universal lever. Default-OFF
    // (XOLVER_NIA_LS_PIN_EQ). Sound by construction: pinning a value
    // forced by an Eq atom never changes the satisfiability of the
    // formula; the pinned move-skip only affects LS heuristic, never
    // verdict (every Sat is still validator-gated).
    void setPinEq(bool e) { pinEq_ = e; }
    // LS-VM3 (master 2026-06-02). When LS plateaus across K consecutive
    // restarts (cost minimum doesn't improve), break out early and run
    // a CHEAP coefficient-GCD modular check on the equality atoms. If
    // any `c*x*y + ... + k = 0` atom has gcd(coefficients) ∤ k, the
    // atom (and hence the formula) has no integer solution — but LS
    // alone cannot soundly claim UNSAT, so the check is informational
    // and just lets us exit LS sooner (saving budget for upstream
    // engines and/or downstream stages that DO emit UNSAT verdicts).
    // The early exit also helps UNSAT-leaning cases where LS would
    // otherwise burn all restarts to no avail. XOLVER_NIA_LS_MODULAR_ESCALATE
    // default-OFF. Sound: LS still never claims UNSAT.
    void setModularEscalate(bool e) { modularEscalate_ = e; }
    // Reset the persistent LS context (e.g. on solver reset / backtrack
    // beyond the level where the context was populated). Exposed for
    // NiaSolver to call from onBacktrack / onReset, and for tests.
    void resetLsContext() { lsContext_.reset(); }
    // Read-only access to the persistent context (Phase L1 step 3 hooks:
    // NiaSolver reads varActivity for decision-priority boost; reads
    // bestAssignment to seed a candidate at decide time).
    const NiaLsContext& lsContext() const { return lsContext_; }

private:
    PolynomialKernel& kernel_;
    long budgetMs_;
    long totalBudgetMs_;
    long cumulativeMs_ = 0;
    bool enhanced_ = false;
    bool twoLevel_ = false;
    bool warmStart_ = false;
    bool multiScale_ = false;
    bool quadCritical_ = false;
    bool fsJump_ = false;
    bool diverseInit_ = false;
    bool bilinearPair_ = false;
    bool bilinearSubst_ = false;
    bool pinEq_ = false;
    bool modularEscalate_ = false;
    NiaLsContext lsContext_;

    mpz_class violation(const IntegerModel& model,
                        const std::vector<NormalizedNiaConstraint>& constraints) const;

    // WalkSAT with discrete-Newton critical moves: pick a violated constraint,
    // jump a variable toward the value that satisfies it (Yices2-style
    // accelerated hill-climbing + feasible-set jumping), with random noise and
    // restarts to escape local minima. Returns a satisfying assignment or
    // nullopt; the result is a candidate only (the caller validates it), so the
    // search is always sound regardless of heuristic choices.
    std::optional<IntegerModel> walkSat(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const std::vector<std::string>& vars,
        const DomainStore& domains);

    // Phase L1: enhanced WalkSAT with incremental clause-violation tracking
    // (O(affected) per move instead of O(n) full re-evaluation), PAWS
    // clause weights (hard clauses accumulate weight on plateau), and
    // accelerated hill-climb with adaptive step size (acc=1.2 successive:
    // step, step*acc, step*acc^2). Falls back semantically to walkSat
    // (same Sat-finder contract — candidate only, validator-gated).
    std::optional<IntegerModel> walkSatTwoLevel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const std::vector<std::string>& vars,
        const DomainStore& domains);
};

} // namespace xolver
