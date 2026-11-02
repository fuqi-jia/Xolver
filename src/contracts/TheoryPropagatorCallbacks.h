#pragma once

#include "contracts/TheoryAtomTypes.h"
#include "contracts/TheoryAssignmentView.h"

namespace xolver {

// ---------------------------------------------------------------------------
// Thin lookup interface for querying theory atoms by SAT variable.
// Breaks the dependency of sat/CadicalTheoryPropagator on TheoryAtomRegistry.
// ---------------------------------------------------------------------------
class TheoryAtomLookup {
public:
    virtual ~TheoryAtomLookup() = default;
    virtual const TheoryAtomRecord* findBySatVar(SatVar v) const = 0;
    // Linear candidates from an append-only registration suffix. The offset
    // counts ALL records, matching numAtomVars(), including non-linear atoms.
    // Omitting it returns an owned snapshot of all linear candidates.
    virtual std::vector<SatVar> linearAtomVars(size_t firstRecord = 0) const {
        std::vector<SatVar> result;
        const auto atoms = allAtomVars();
        for (size_t i = firstRecord; i < atoms.size(); ++i) {
            const auto* atom = findBySatVar(atoms[i]);
            if (atom && std::holds_alternative<LinearAtomPayload>(atom->payload))
                result.push_back(atoms[i]);
        }
        return result;
    }
    // SatVars of ALL registered theory atoms (linear, polynomial, shared-eq,
    // EUF-eq, ...). Used by cb_decide to break the combination livelock:
    // shared-equality / interface atoms are OBSERVED but appear in no
    // irredundant clause, so CaDiCaL cannot VSIDS-decide them and spins on
    // cb_decide without completing a model. Default empty.
    virtual std::vector<SatVar> allAtomVars() const { return {}; }
    // Count registered atoms so decision snapshots can detect dynamic growth.
    // Registries override this with an O(1) count; custom lookups inherit a
    // count consistent with their enumeration rather than an unknown zero.
    virtual size_t numAtomVars() const { return allAtomVars().size(); }
};

// ---------------------------------------------------------------------------
// Thin storage interface for theory lemmas.
// Breaks the dependency of sat/CadicalTheoryPropagator on TheoryLemmaDatabase.
// ---------------------------------------------------------------------------
class TheoryLemmaStorage {
public:
    virtual ~TheoryLemmaStorage() = default;
    virtual bool contains(const TheoryLemma& lemma) const = 0;
    virtual bool insertIfNew(const TheoryLemma& lemma) = 0;
    virtual bool isInstalled(const TheoryLemma& lemma) const { (void)lemma; return false; }
    virtual void markInstalled(const TheoryLemma& lemma) { (void)lemma; }
};

// ---------------------------------------------------------------------------
// Thin callback interface for theory propagation from SAT solver.
// Breaks the dependency of sat/CadicalTheoryPropagator on TheoryManager.
// ---------------------------------------------------------------------------
class TheoryPropagationCallbacks {
public:
    virtual ~TheoryPropagationCallbacks() = default;

    virtual void assertTheoryLit(const TheoryAtomRecord& atom, SatLit lit, int level) = 0;
    virtual void backtrackToLevel(int level) = 0;
    virtual void restoreRootLiteral(const TheoryAtomRecord& atom, SatLit lit) {
        assertTheoryLit(atom, lit, 0);
    }
    virtual void setAssignmentView(TheoryAssignmentView* view) = 0;
    virtual TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) = 0;

    // Whether the theory stack runs in Nelson-Oppen combination mode. Lets the
    // SAT propagator scope combination-only policies (e.g. the Standard-effort
    // early-conflict deferral floor) without depending on TheoryManager.
    virtual bool isCombinationMode() const { return false; }
    // Drain ENTAILMENT-class theory propagations buffered during the most recent
    // check() (e.g. LRA Farkas row-propagations). Default empty. Implementations
    // must return ONLY unconditional entailments (never Guess/branch lemmas) and
    // must return nothing in combination mode (shared-bus interaction is out of
    // scope). The propagator additionally verifies each clause is unit/falsified
    // under the current assignment before installing it.
    virtual std::vector<TheoryLemma> takeEntailmentPropagations() { return {}; }

    // Heuristic: is the bound atom `v` TRUE at the current (possibly stale)
    // theory model? Used by cb_decide to steer the SAT search toward a
    // theory-feasible region. Heuristic only — a wrong answer costs a backtrack,
    // never soundness (the verdict is still theory-gated + model-validated).
    // nullopt = no value / not a theory atom this theory can evaluate.
    virtual std::optional<bool> evalTheoryAtom(SatVar v) { (void)v; return std::nullopt; }
};

} // namespace xolver
