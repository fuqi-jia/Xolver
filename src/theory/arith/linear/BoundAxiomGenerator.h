#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>
#include <optional>

namespace zolver {

class TheoryAtomRegistry;

// ---------------------------------------------------------------------------
// BoundAxiomGenerator (ZOLVER_LRA_BOUND_AXIOMS, default OFF)
//
// For each group of linear atoms sharing the SAME linear form L (same terms
// AND coefficients), emits the theory-tautology binary clauses relating their
// boolean literals, e.g.
//     (L <= 3)  =>  (L <= 5)            : (¬p1 ∨ p2)
//     ¬((L <= 3) ∧ (L >= 5))            : (¬p1 ∨ ¬p2)
//     (L <= 3) ∨ (L >= 1)               : ( p1 ∨ p2)   [union covers ℝ]
//
// These are branch-independent tautologies (true for ALL real L), so adding
// them to the SAT core is sound: it removes no real model, it only lets BCP
// propagate bound implications the SAT solver could not otherwise see —
// eliminating the immediate-bound-conflict churn (size-2 theory conflicts)
// at the root. No simplex / propagation-callback changes.
//
// Soundness is in the exact truth-set logic below; it is unit-tested against
// brute-force ground truth over rationals for every relation/strictness combo.
// ---------------------------------------------------------------------------
class BoundAxiomGenerator {
public:
    // Truth-set of an atom (L rel c), as an interval over ℝ.
    //   valid=false  => relation not handled (e.g. Neq: complement of a point)
    struct Interval {
        bool valid = false;
        bool loInf = true;     // lower endpoint is -inf
        bool hiInf = true;     // upper endpoint is +inf
        mpq_class lo;          // valid iff !loInf
        mpq_class hi;          // valid iff !hiInf
        bool loIncl = false;   // lower endpoint included (closed)
        bool hiIncl = false;   // upper endpoint included (closed)
    };

    // Convert (rel, c) to its truth-set interval. Neq -> invalid (skipped).
    static Interval toInterval(Relation rel, const mpq_class& c);

    // Exact set relations (both intervals assumed valid & non-empty).
    static bool subset(const Interval& a, const Interval& b);    // a ⊆ b
    static bool disjoint(const Interval& a, const Interval& b);  // a ∩ b = ∅
    static bool covers(const Interval& a, const Interval& b);    // a ∪ b = ℝ

    // Clause shapes a pair of literals (pA for atom A, pB for atom B) implies.
    enum class Shape { ImpAtoB, ImpBtoA, Exclusion, Cover };
    // Returns the tautological clause shapes for (relA,cA) vs (relB,cB).
    static std::vector<Shape> pairShapes(Relation relA, const mpq_class& cA,
                                         Relation relB, const mpq_class& cB);

    // Enumerate registry linear atoms, group by form, emit clauses to `sat`.
    // No-op unless ZOLVER_LRA_BOUND_AXIOMS is set. Returns #clauses emitted.
    static int generate(const TheoryAtomRegistry& registry, SatSolver& sat);

private:
    static bool enabled();
    static int maxGroupSize();
};

} // namespace zolver
