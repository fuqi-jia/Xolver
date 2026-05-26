#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryAssignmentView.h"

namespace zolver {

// ---------------------------------------------------------------------------
// Thin lookup interface for querying theory atoms by SAT variable.
// Breaks the dependency of sat/CadicalTheoryPropagator on TheoryAtomRegistry.
// ---------------------------------------------------------------------------
class TheoryAtomLookup {
public:
    virtual ~TheoryAtomLookup() = default;
    virtual const TheoryAtomRecord* findBySatVar(SatVar v) const = 0;
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
    virtual void setAssignmentView(TheoryAssignmentView* view) = 0;
    virtual TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) = 0;

    // Whether the theory stack runs in Nelson-Oppen combination mode. Lets the
    // SAT propagator scope combination-only policies (e.g. the Standard-effort
    // early-conflict deferral floor) without depending on TheoryManager.
    virtual bool isCombinationMode() const { return false; }
};

} // namespace zolver
