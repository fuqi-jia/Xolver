#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/types.h"

#include <vector>

namespace xolver {

class PolynomialKernel;

// ============================================================================
// CAC single-cell projection (lever 3, module B — see ../CAC.md).
//
// `characterize` is the projection step the conflict-driven covering performs
// in place of a full Collins closure: given the polynomials relevant to the
// current cell (all with main variable `elimVar`) it emits, via the COMPLETE
// Lazard operator (`lazardProjectStep`), the polynomials needed one level down.
// The result is partitioned by whether each output still contains `elimVar`:
//
//   * boundaryPolys — still contain elimVar; their real roots (isolated at the
//     sample prefix) delineate elimVar's axis at THIS level.
//   * downwardPolys — do NOT contain elimVar (leading/trailing coefficients,
//     discriminants, pairwise resultants, contents); they are the cell
//     polynomials for the NEXT level down.
//
// SOUNDNESS: `complete == false` (the Lazard operator hit an exact-gcd/budget
// limit) ⇒ the caller MUST NOT rest UNSAT on this characterization (⇒ Unknown).
// The Lazard operator is unconditionally sound when complete (no
// well-orientedness precondition), so no false-UNSAT can arise from a complete
// characterization.
//
// Pure given a kernel (the libpoly-backed exact gcd/psc path for high degree);
// `kernel == nullptr` uses the hand-rolled path (low-degree, for tests).
// ============================================================================

struct CharacterizationResult {
    bool complete = true;
    std::vector<RationalPolynomial> boundaryPolys;   // contain elimVar (this level)
    std::vector<RationalPolynomial> downwardPolys;    // free of elimVar (next level)
};

CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel = nullptr);

} // namespace xolver
