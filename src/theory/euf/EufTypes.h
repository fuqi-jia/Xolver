#pragma once
#include "expr/types.h"
#include "sat/SatSolver.h"
#include "theory/core/TheoryAtomTypes.h"
#include <vector>
#include <string>
#include <cstdint>
#include <limits>

namespace xolver {

using EufTermId = uint32_t;
using EClassId = uint32_t;
using FuncSymbolId = uint32_t;
using MergeId = uint32_t;


constexpr EufTermId NullEufTerm = std::numeric_limits<EufTermId>::max();
constexpr EClassId NullEClass = std::numeric_limits<EClassId>::max();
constexpr FuncSymbolId NullFunc = std::numeric_limits<FuncSymbolId>::max();
constexpr MergeId NullMergeId = std::numeric_limits<MergeId>::max();

struct EufAtom {
    EufTermId lhs;
    EufTermId rhs;
    Relation rel;
    SatLit assertedLit;
};

enum class MergeReasonKind {
    AssertedEquality,
    Congruence,
    BuiltinEval,
    // Array axiom merges with NO governing SAT literal. Like BuiltinEval, they
    // contribute zero literals to a conflict explanation (the equality is a
    // theory tautology). ArrayRow1: select(store(a,i,v),i) = v.
    // ArrayConst: select(const(v),i) = v.
    // ArrayRow2: select(store(a,i,v),j) = select(a,j) when i,j are distinct
    // constants (i != j is built into the literals, so the Row2 conclusion is
    // unconditional — zero literals, no SAT split needed).
    ArrayRow1,
    ArrayConst,
    ArrayRow2,
    // CONDITIONAL Row2 (L2): select(store(a,i,v),j) = select(a,j) merged eagerly
    // when i≠j is KNOWN-disequal in the e-graph (vs the unconditional distinct-
    // CONSTANT case ArrayRow2). Unlike ArrayRow2 it is NOT a free tautology: it
    // rests on the disequality's reason. The explanation therefore contributes
    // `lit` (the diseq reason literal) AND recurses on argPairs (the equality
    // chains i~diseqLhs, j~diseqRhs). Merged at currentLevel_ so any backtrack
    // touching its justification removes it (never stale → no wrong-UNSAT).
    ArrayRow2Cond
};

struct MergeReason {
    MergeReasonKind kind;
    SatLit lit;
    EufTermId lhsApp = NullEufTerm;    // Congruence / Axiom
    EufTermId explainA = NullEufTerm;
    EufTermId explainB = NullEufTerm;
    std::vector<std::pair<EufTermId, EufTermId>> argPairs;
};

enum class MergeStatus {
    Ok,
    SortMismatch
};

enum class CloseStatus {
    Ok,
    SortMismatch
};

struct MergeResult {
    bool merged;
    EClassId kept;   // winner root
    EClassId killed; // loser root
};

struct MergeRecord {
    MergeId id;
    EufTermId lhs;
    EufTermId rhs;
    EClassId lhsRootBefore;
    EClassId rhsRootBefore;
    EClassId kept = NullEClass;
    EClassId killed = NullEClass;
    bool merged = false;
    MergeReason reason;
    // SAT decision level at which this merge was caused (level of the asserted
    // equality or, for congruence merges, the level of the parent merge that
    // triggered the saturation). Used by EufSolver::backtrackToLevel to filter
    // out merges whose level > target in a SECOND pass after the count-based
    // egraph rollback — the count-based snapshot assumes monotonic level order
    // in mergeRecords_ which combination interface equalities violate, leaving
    // stale Congruence edges that survive backtrack and produce wrong UNSAT
    // (Wisa xs-10-08 class). Default 0 = pre-fix records / asserted at level 0.
    int level = 0;
};

struct EGraphSnapshot {
    size_t ufTrailSize = 0;
    size_t memberTrailSize = 0;
    size_t mergeRecordSize = 0;
    size_t sigTableSnap = 0;
    size_t currentSigSnap = 0;
    size_t proofForestSnap = 0;
    EufTermId nextTermToRegister = 0;
};

struct MemberChange {
    EClassId dstRoot;
    EClassId srcRoot;
    size_t oldDstSize;
};

struct ExplainResult {
    bool ok;
    std::vector<SatLit> reasons;
};

} // namespace xolver
