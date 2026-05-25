#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"
#include "theory/arith/nra/core/CdcacValue.h"   // RootSet, RealAlg
#include "expr/types.h"

namespace nlcolver {

// ---------------------------------------------------------------------------
// TowerRootIsolation — real roots over a tower (LAZARD.md [H2]).
//
// Two stages: (1) Norm candidate generation (this file, B.2.a) — the iterated
// resultant eliminating every extension variable A_i against its minimal poly
// m_i, leaving a univariate N(mainVar) over Q whose real roots are a SUPERSET
// of the true roots (it mixes conjugate branches); (2) exact filter (B.2.b,
// not yet implemented) — keep a candidate beta iff F(beta) = 0 at the chosen
// real embedding, deleting extraneous/conjugate roots; inconclusive => Unknown.
//
// SOUNDNESS NOTE: the Norm alone is NOT a usable root set — its extra roots
// would create bogus SECTION cells (x = beta with F(beta) != 0), which is
// UNSOUND. Until the exact filter lands, isolateRealRootsInTower reports
// supported = false (caller => Unknown, never UNSAT).
// ---------------------------------------------------------------------------

// Norm over Q of F (a polynomial in the extension variables + mainVar): eliminate
// every extension variable against its minimal poly. Result is in Q[mainVar].
// ok == false on a resultant-submatrix budget overflow or a degenerate
// elimination (caller treats as incomplete => Unknown).
struct TowerNormResult {
    RationalPolynomial norm;   // in mainVar only (when ok)
    bool ok = true;
};
TowerNormResult towerNorm(const RationalPolynomial& F, VarId mainVar,
                          const TowerContext& ctx, int maxMatrixDim = 12);

// [H2] full real-root isolation over a tower. B.2.b will implement the exact
// filter (needs tower field division + irreducible minimal polys). Until then
// this is intentionally unsupported (sound: caller => Unknown).
struct TowerRootResult {
    bool supported = false;
    RootSet roots;
};
TowerRootResult isolateRealRootsInTower(const RationalPolynomial& F, VarId mainVar,
                                        const TowerContext& ctx);

}  // namespace nlcolver
