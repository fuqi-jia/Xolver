#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include "util/RealValue.h"
#include <vector>
#include <optional>
#include <unordered_map>
#include <functional>
#include <string>

namespace zolver {

class TheoryLemmaStorage;
class CareGraph;

// ---------------------------------------------------------------------------
// Abstract interface for theory solvers
// ---------------------------------------------------------------------------

class TheorySolver {
public:
    virtual ~TheorySolver() = default;

    virtual TheoryId id() const = 0;

    // Scope management (for Solver::push/pop API)
    virtual void push() = 0;
    virtual void pop(uint32_t n) = 0;

    // Incremental assertion from SAT trail
    virtual void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) = 0;

    // Backtrack to target decision level
    virtual void backtrackToLevel(int level) = 0;

    // Check current incremental state
    virtual TheoryCheckResult check(TheoryLemmaStorage& lemmaDb,
                                    TheoryEffort effort = TheoryEffort::Standard) = 0;

    // Reset ONCE per fresh check-sat initialization
    virtual void reset() = 0;

    // Sound Farkas bound-propagations to lift to the SAT solver as entailment
    // lemmas (ZOLVER_LRA_PROP). Default: none. Must never return Guess/branch lemmas.
    virtual std::vector<TheoryLemma> takeEntailmentPropagations() { return {}; }

    // Heuristic eval of a bound atom at the current theory model
    // (ZOLVER_LRA_DECIDE / cb_decide). Default: no value.
    // Heuristic eval of a bound atom at the current theory model (see
    // TheoryPropagationCallbacks::evalTheoryAtom). Default: no value.
    virtual std::optional<bool> evalAtomAtModel(SatVar v) { (void)v; return std::nullopt; }

    // -----------------------------------------------------------------------
    // Active linear context for nonlinear solvers (optional; default = no-op)
    // -----------------------------------------------------------------------
    virtual void setActiveLinearContext(const std::vector<ActiveLinearConstraint>* context) {
        (void)context;
    }

    // -----------------------------------------------------------------------
    // Nelson-Oppen combination hooks (optional; default = no-op)
    // -----------------------------------------------------------------------
    virtual bool supportsCombination() const { return false; }

    // Care graph (ZOLVER_COMB_CAREGRAPH). TheoryManager hands the built care
    // graph to each solver so the O(n^2) getDeducedSharedEqualities loops can
    // skip shared-term pairs no theory cares about. Non-null only when the flag
    // is on AND the graph is built; default no-op keeps the pointer null and the
    // loops unchanged. Pruning is sound (skipping loses only completeness,
    // caught by ModelValidator -> Unknown, never wrong UNSAT).
    virtual void setCareGraph(const CareGraph* cg) { (void)cg; }

    virtual TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) {
        (void)a; (void)b; (void)reason; (void)level;
        return TheoryCheckResult::consistent();
    }

    virtual TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) {
        (void)a; (void)b; (void)reason; (void)level;
        return TheoryCheckResult::consistent();
    }

    struct SharedEqualityPropagation {
        SharedTermId a;
        SharedTermId b;
        std::vector<SatLit> reasons;
    };

    virtual std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() { return {}; }

    // Bounded atom-level Gaussian implied equalities, SCOPED to the given (few)
    // array-index shared-var pairs (the combination layer supplies them at Full
    // effort). For each pair (a,b), tests whether a-b == 0 is entailed by the
    // asserted linear EQUALITY atoms — i.e. whether (e_a - e_b) lies in the
    // row-space of the equality system (a linear COMBINATION of asserted equalities
    // yields a-b=0). This catches equalities that the per-atom same-form/2-var
    // detectors miss (read2: bz+ba = x+y via ba=x+y-bz, distinct definitional
    // forms). Reason = the combining atom literals (sound and complete). Done at
    // the atom level (small Gaussian over coefficient rows), never via the simplex
    // tableau. Default: none (only LIA/LRA implement it).
    virtual std::vector<SharedEqualityPropagation>
    deduceIndexEqualitiesByGaussian(const std::vector<SharedTermId>& idxTerms) {
        (void)idxTerms; return {};
    }

    // SharedTermIds used as ARRAY INDEX terms (only the EUF/array solver answers).
    // The combination layer uses this to scope deduced-equality propagation to
    // array-index pairs at Full effort: a pending array Row1/Row2 needs the
    // entailed index equality, but propagating EVERY deduced equality at Full
    // floods the SAT core (broad regressions). Default empty.
    virtual std::vector<SharedTermId> arrayIndexSharedTerms() const { return {}; }

    // Nelson-Oppen arrangement support: the current arith-model value of a
    // shared scalar term, if this solver owns it and has a concrete value.
    // Used by model-based arrangement splitting to detect when two shared
    // scalars are assigned the same value by arith but are not merged in EUF.
    // Default: no value (non-arith solvers).
    virtual std::optional<RealValue> sharedTermArithValue(SharedTermId s) const {
        (void)s;
        return std::nullopt;
    }

    // Nelson-Oppen arrangement support: are the two shared terms currently in
    // the same equivalence class on this solver's side? Only the EUF solver
    // answers meaningfully; default false (not-merged / cannot tell).
    virtual bool sharedTermsMerged(SharedTermId a, SharedTermId b) const {
        (void)a; (void)b;
        return false;
    }

    // Nelson-Oppen arrangement support: are the two shared terms ACTIVELY
    // DISEQUAL on this solver's side — i.e. does it hold an asserted/derived
    // disequality (a-b != 0, e.g. a native (distinct a b))? The combination
    // certificate uses this to EXCLUDE a model-coinciding shared-arg pair from
    // being a congruence obligation: if a != b is asserted, the coincidence is a
    // model artifact (a valid model separates them), not an undischarged
    // congruence — so the SAT verdict is recoverable (this is the uflra_007
    // over-floor fix). SUFFICIENT only (may miss a derived disequality); a miss
    // merely keeps the conservative floor, never removes a real obligation, so it
    // is sound. Default false.
    virtual bool sharedTermsActivelyDisequal(SharedTermId a, SharedTermId b) const {
        (void)a; (void)b;
        return false;
    }

    // Nelson-Oppen arrangement support: the combination layer calls this on the
    // arith solver when it emits a model-based arrangement SPLIT over (a,b). It
    // authorizes the arith solver to MODEL-BRANCH a later DECIDED interface
    // disequality on exactly this pair — i.e. to split the convex model apart
    // when it equates two terms the SAT solver decided unequal. Scoping the
    // model-branch to arrangement-split pairs keeps it from perturbing array
    // disequalities the array reasoner itself manages (those are NOT authorized
    // and the convex model is left to the existing machinery). Default: no-op.
    virtual void allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) {
        (void)a; (void)b;
    }

    // Phase 0 combination SAT certificate (positive-completeness proof). Returns
    // true ONLY if this solver can POSITIVELY certify that its current state is a
    // COMPLETE, consistent SAT model — every obligation discharged (EUF: congruence
    // closed + all asserted (dis)equalities hold + no pending merge/array obligation;
    // LIA: simplex consistent + integral + all interface (dis)equalities honored).
    // FAIL-CLOSED: the default is `false` — a solver that cannot prove completeness
    // (e.g. an undetected obligation type) must NOT be trusted, so the combination
    // floor downgrades to sound Unknown. `reason` (optional) names what blocked the
    // certificate, for diagnostics.
    virtual bool satComplete(std::string* reason = nullptr) const {
        if (reason) *reason = "theory has no completeness certificate";
        return false;
    }

    // Phase 1 combination-arrangement detector (EUF override). True iff a pending
    // UF-argument arrangement (shared bridge-vars/args value-equal but not merged,
    // so an application congruence is undischarged) blocks completeness. Default
    // false (only EUF owns congruence). `valueEqual` compares two shared terms'
    // arith-model values, supplied by the combination layer.
    virtual bool hasUnarrangedUfCongruence(
        const std::function<bool(SharedTermId, SharedTermId)>& valueEqual,
        std::string* reason = nullptr) const {
        (void)valueEqual; (void)reason;
        return false;
    }

    // Phase 1 arrangement (recovery): the shared-term argument pairs to split
    // (a=b ∨ a≠b) so an undischarged UF-application congruence is resolved.
    // Default empty (only EUF owns congruence). See EufSolver override.
    virtual std::vector<std::pair<SharedTermId, SharedTermId>>
    collectArrangeableUfArgPairs(
        const std::function<bool(SharedTermId, SharedTermId)>& valueEqual) const {
        (void)valueEqual;
        return {};
    }

    struct TheoryModel {
        // variable name -> value string (e.g. "x" -> "42", "y" -> "3/4").
        // Legacy channel; carries both numeric and boolean values as strings.
        std::unordered_map<std::string, std::string> assignments;
        // Typed numeric channel (RealValue unification, Phase 1). Solvers that
        // have migrated populate this; consumers prefer it for arithmetic
        // variables and fall back to `assignments` otherwise. Lets NRA export
        // exact algebraic models (e.g. √2) instead of a lossy string.
        std::unordered_map<std::string, RealValue> numericAssignments;

        // Interpretation of an uninterpreted function symbol as a finite
        // table plus a default. Each entry maps a concrete argument tuple to
        // a value; arguments not in the table take `deflt`. Populated by the
        // validated candidate search for QF_UF* model output (get-model).
        struct FuncEntry {
            std::vector<std::string> args;  // one value string per argument
            std::string value;
        };
        struct FuncInterp {
            std::vector<std::string> argSorts;  // "Int"/"Real"/"Bool" per arg
            std::string retSort;
            std::vector<FuncEntry> entries;
            std::string deflt;                  // value for unlisted tuples
        };
        std::unordered_map<std::string, FuncInterp> functionInterps;

        // Interpretation of an array variable: a default element plus a finite
        // set of (index, element) overrides. Equal arrays share one interp.
        // `defaultVal` is the value at any index not listed in `entries`.
        // Index/element values are opaque tokens that compare by equality
        // (e.g. eclass-rep markers like "@arr_e7"), since QF_AX indices and
        // elements may be uninterpreted-sort. Populated by EufSolver::getModel.
        struct ArrayInterp {
            std::string indexSort;
            std::string elemSort;
            std::string defaultVal;
            std::vector<std::pair<std::string, std::string>> entries; // (index, value)
        };
        std::unordered_map<std::string, ArrayInterp> arrayInterps;
    };
    virtual std::optional<TheoryModel>
    getModel() const { return std::nullopt; }
};

// Legacy struct (for backward compatibility during transition)
struct TheoryAtom {
    SatVar satVar;
    ExprId exprId;
};

} // namespace zolver
