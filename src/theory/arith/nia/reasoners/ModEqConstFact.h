#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>

namespace xolver {

// Track A Phase 1.1 — native ModEqConst fact representation.
//
// For an asserted equality of the shape `(= (mod x y) c)` (or symmetric)
// the front-end MAY register a ModEqConstFact instead of letting
// IntDivModLowerer eagerly emit the variable-divisor nonlinear constraint
// system `x = y*q + r ∧ 0 ≤ r < |y|`. The native ModEqConst reasoner then
// reasons about the fact directly using divisibility / sign / bound rules,
// avoiding manufacturing `y*q` (which the legacy NIA pipeline cannot
// decide within budget for LCTES-class formulas).
//
// Semantics of `(mod x y) = c` under SMT-LIB Int semantics:
//   y = 0:  mod0(x,y) = c           (uninterpreted, EUF semantics)
//   y > 0:  c >= 0, y >= c+1,  y | (x - c)
//   y < 0:  c >= 0, -y >= c+1, y | (x - c)
//
// The fact is sound to emit when both x and y are integer-sorted and c is
// an integer constant. The reasoner derives conflicts/domain updates from
// these semantics.
//
// Soundness: every rule the reasoner applies derives either:
//   - Conflict: a sound UNSAT clause over the asserted reasons
//   - DomainUpdated: a narrowing of an existing variable domain with
//     the asserted reasons as the propagation witness
// No rule materializes `y*q` lazily UNLESS Phase 1.5 budget elapses, at
// which point the existing emitVariableDivisorConstraints path is taken
// as a fallback (no soundness change vs the default-OFF behavior).
struct ModEqConstFact {
    ExprId xExpr;     // dividend
    ExprId yExpr;     // divisor (variable)
    mpz_class c;      // constant remainder

    // ExprId of the original asserted (= (mod x y) c) atom (or its negation
    // when the polarity is false). Used to gate the fact on the current
    // SAT assignment and to build conflicts/explanations.
    ExprId atomExpr;
    SatLit reason;    // SAT literal whose assignment activates this fact
                      // (positive lit → fact active when true)
};

// Storage container — owned by the NIA solver. Append-only during preprocess.
// Activation is dynamic (driven by assertLit in the SAT trail).
using ModEqConstFactList = std::vector<ModEqConstFact>;

}  // namespace xolver
