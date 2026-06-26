// Newton-Raphson integer-sqrt invariant prover.
//
// Target: sqrtStep1.smt2 / sqrtStep1a.smt2 (corpus oracle-UNSAT).
// See docs/newton-integer-sqrt-analysis.md for the full algebraic
// derivation. Summary:
//
//   Pattern:  (= V (div (+ U (div X U)) 2))
//   With hypothesis: (<= (* U U) X) ∧ (<= X (* 4 (* U U)))
//   The branch `X >= (V+1)*(V+1)` is algebraically UNSAT because
//   the inequality
//     (newres - oldres + 1)^2 + 1 <= 0
//   has no integer solutions. (Completed-square contradiction.)
//
// This prover detects the template, validates hypothesis, and emits
// the corresponding theory lemma into NiaSolver's lemma queue.
//
// Gated by XOLVER_PP_NEWTON_INT_SQRT (default-OFF).

#pragma once

#include "expr/types.h"
#include <optional>
#include <vector>

namespace xolver {

class CoreIr;

namespace newton {

struct IntSqrtRecurrence {
    ExprId oldres;       // U
    ExprId x;            // X
    ExprId newres;       // V
    ExprId defAtom;      // the original (= V (div ...)) atom
    // Provable bounds (set if found in the formula):
    bool hasLowerBound = false;  // (<= (* U U) X)
    bool hasUpperBound = false;  // (<= X (* C (* U U))) for some C >= 1
    // The branch-1 contradiction atom: emitted as a lemma.
    //   (=> hypotheses (< X (* (+ V 1) (+ V 1))))
    ExprId branchOneLemma = NullExpr;
};

// Scan the CoreIr's top-level assertions for integer-sqrt Newton
// templates. For each recognised template, build the branch-1
// contradiction lemma and return them. Caller can submit the lemmas
// into NiaSolver's TheoryLemmaStorage.
//
// Returns an empty vector if no template matches OR if the hypotheses
// don't hold in the asserted formula.
std::vector<IntSqrtRecurrence>
detectAndProveIntSqrt(CoreIr& ir, SortId boolSort);

} // namespace newton
} // namespace xolver
