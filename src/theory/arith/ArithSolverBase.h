#pragma once

#include "theory/core/TheorySolver.h"
#include <algorithm>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

class Reasoner;
class CoreIr;
class SharedTermRegistry;

/**
 * ArithSolverBase — shared base for the arithmetic theory solvers
 * (LRA, LIA, NRA, NIA, NIRA, LIRA, IDL, RDL).
 *
 * Consolidates the boilerplate that was copy-pasted across solvers:
 *
 *   1. The assignment trail. Every arith solver tracked active SAT
 *      assignments in an identical
 *          struct ActiveAssignment { int level; SatLit lit;
 *                                    TheoryAtomRecord atom; bool value; };
 *          std::vector<ActiveAssignment> activeAssignments_;
 *      with the same dedup-by-satVar insert and remove-by-level
 *      backtrack. That lives here now, in `state_.trail`.
 *
 *   2. Scope counters and the `currentLevel` bookkeeping.
 *
 *   3. An OPTIONAL generic pending-result slot
 *      (`state_.pending`). A solver that needs exactly one deferred
 *      Conflict/Lemma/Unknown carrying a decision level can use the
 *      record/drain helpers. Solvers whose pending semantics don't fit
 *      a single slot (e.g. a solver that wants a Conflict AND a Lemma
 *      live simultaneously) keep their own optionals — they still get
 *      the trail consolidation.
 *
 * Behaviour preservation contract: `assertLit`, `backtrackToLevel`,
 * `push`, `pop`, and `reset` are finalized here to reproduce the EXACT
 * pre-refactor semantics:
 *   - assertLit: if an assignment with the same satVar already exists
 *     on the trail, REPLACE it in place; otherwise append. Then call
 *     onAssertLit().
 *   - backtrackToLevel(L): drop every trail entry with level > L, clear
 *     any pending whose level > L, set currentLevel = L, then call
 *     onBacktrack(L).
 *   - push/pop: default to scope-counter bookkeeping plus the onPush/
 *     onPop hooks (most arith solvers historically made these no-ops;
 *     the CDCL(T) trail is driven by assertLit/backtrackToLevel, not
 *     push/pop).
 *   - reset: clear all state_, then call onReset().
 *
 * Subclasses implement the three pure hooks (onAssertLit, onBacktrack,
 * onReset) and may override onPush/onPop.
 */
class ArithSolverBase : public TheorySolver {
public:
    // Out-of-line dtor: `reasoners_` is a vector<unique_ptr<Reasoner>>
    // over a forward-declared Reasoner, so the destructor must be defined
    // in the .cpp (where Reasoner.h is complete).
    ArithSolverBase();
    ~ArithSolverBase() override;

    // ----- TheorySolver interface -----
    // push/pop/backtrackToLevel/reset are finalized: every arith solver
    // shares the trail roll-back + scope semantics, and customizes via
    // the onX hooks. assertLit is VIRTUAL (not final): most solvers use
    // the default dedup-by-satVar insert, but NIA needs a different
    // admission policy (ActiveLiteralSet dedup + opposite-polarity
    // detection), so it overrides assertLit while still driving the
    // shared `state_.trail`.
    void push() final;
    void pop(uint32_t n) final;
    void assertLit(const TheoryAtomRecord& atom, bool value,
                   int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) final;
    void reset() final;

    // Default check(): drain any pending result, then walk the reasoner
    // pipeline (Phase 2). A solver that has populated `reasoners_` in its
    // constructor gets a uniform check() for free — the first stage
    // returning a non-Consistent verdict wins. Solvers not yet decomposed
    // into reasoners override check() as before. A solver with an empty
    // `reasoners_` and no override would always report Consistent, so the
    // pipeline is only the verdict when reasoners_ is non-empty.
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb,
                            TheoryEffort effort = TheoryEffort::Standard) override;

    // Names of the registered reasoner stages, in pipeline order. For testing
    // and diagnostics; reflects the order stages run in check(). Defined in the
    // .cpp so the header keeps only a forward declaration of Reasoner.
    std::vector<std::string> reasonerNames() const;

    // ----- Shared frontend hooks (hoisted from per-solver duplicates) -----
    // CoreIr and SharedTermRegistry pointers are set by TheoryFactory /
    // SolverImpl during combination setup. Every arith solver had its own
    // pair of (field + setter) duplicating this contract; they live on the
    // base now. setCoreIr is virtual so solvers that need post-set side
    // effects (NIA's Farkas dump) can override; the base still sets coreIr_.
    virtual void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) {
        sharedTermRegistry_ = reg;
    }

protected:
    // ----- Reasoner pipeline (Phase 2) -----
    // Populated in a subclass constructor; walked by the default check().
    std::vector<std::unique_ptr<Reasoner>> reasoners_;

    // Walk reasoners_ in order: drain pending first, then run each stage
    // whose runsAt(effort) holds; return the first non-Consistent verdict,
    // else Consistent. Exposed so a solver that needs custom pre/post
    // logic can call it from its own check() override.
    TheoryCheckResult runReasonerPipeline(TheoryLemmaStorage& lemmaDb,
                                          TheoryEffort effort);

    // ----- Shared trail entry (was duplicated 56× across solvers) -----
    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };

    // ----- Generic level-tagged pending result -----
    struct PendingResult {
        int level;
        TheoryCheckResult result;
    };

    struct TheoryState {
        std::vector<ActiveAssignment> trail;
        std::optional<PendingResult> pending;
        int currentLevel = 0;
        ScopeLevel scopeLevel = 0;
    };
    TheoryState state_;

    // ----- Subclass hooks -----
    // Called after assertLit records the assignment on the trail.
    virtual void onAssertLit(const TheoryAtomRecord& atom, bool value,
                             int level, SatLit assertedLit) {
        (void)atom; (void)value; (void)level; (void)assertedLit;
    }
    // Called after backtrackToLevel rolls back the trail and pendings.
    virtual void onBacktrack(int targetLevel) { (void)targetLevel; }
    // Called after reset wipes state_.
    virtual void onReset() {}
    // Optional push/pop notifications.
    virtual void onPush() {}
    virtual void onPop(uint32_t n) { (void)n; }

    // ----- Pending helpers -----
    void recordPending(int level, TheoryCheckResult result) {
        // Conflict has priority over a previously recorded Lemma/Unknown
        // at the same or lower level — matches the pre-refactor
        // "conflict short-circuits" behaviour.
        if (state_.pending &&
            state_.pending->result.kind == TheoryCheckResult::Kind::Conflict &&
            result.kind != TheoryCheckResult::Kind::Conflict) {
            return;
        }
        state_.pending = PendingResult{level, std::move(result)};
    }
    bool hasPending() const { return state_.pending.has_value(); }
    // Returns the pending result and clears it. Precondition: hasPending().
    TheoryCheckResult drainPending() {
        TheoryCheckResult r = std::move(state_.pending->result);
        state_.pending.reset();
        return r;
    }

    // Convenience: the trail, for subclasses that iterate it.
    const std::vector<ActiveAssignment>& trail() const { return state_.trail; }

    // ----- Frontend / combination state (was duplicated 4× across solvers) -----
    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // SharedTermId -> integer-variable-name lookup cache for the Nelson-Oppen
    // fixed-value seam. Lazily populated on first lookup of each term;
    // invariant for the term's lifetime (the SharedTermRegistry is monotone
    // within a solve, so the name is structural, not assignment-dependent).
    std::unordered_map<SharedTermId, std::string> sharedTermToVarName_;

    // Resolve a shared-term id to the variable name the arith solvers use
    // internally. Returns the variable name when the shared term is an
    // integer/real variable; returns a synthetic "__const_<sharedName>" tag
    // for constant shared terms (LIA's simplex hooks the tag to a synthetic
    // bound; solvers whose DomainStore-equivalent has no entry for the tag
    // simply skip that shared term in their getDeducedSharedEqualities loop).
    // Returns "" when the shared term cannot be resolved (no coreIr, no
    // registry entry, or an unsupported kind) — caller treats "" as skip.
    std::string getVarNameForSharedTerm(SharedTermId s);
};

} // namespace xolver
