#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryAssignmentView.h"

namespace nlcolver {

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
};

} // namespace nlcolver
