#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"
#include "theory/arith/nra/core/CdcacValue.h"   // RootSet, RealAlg
#include "expr/types.h"

namespace zolver {

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

// [H2] full real-root isolation over a tower: Norm candidates -> exact
// root-membership oracle (RootMembershipOracle). `supported` is true ONLY when
// every candidate was exactly decided Keep/Drop; any Unknown => supported=false
// (caller => Unknown, never UNSAT). When supported, `rootIntervals` are the
// kept real roots of F at the embedding, each an isolating interval [lo,hi]
// (lo==hi for a rational root) over the rational defining polynomial `norm`.
// RealAlg construction (needs a kernel for the UniPolyId defining poly) is left
// to the caller (the lifter).
struct TowerRootResult {
    bool supported = false;
    RationalPolynomial norm;                                    // Q defining poly of the roots
    std::vector<std::pair<mpq_class, mpq_class>> rootIntervals;  // kept real roots, ascending
};
TowerRootResult isolateRealRootsInTower(const RationalPolynomial& F, VarId mainVar,
                                        const TowerContext& ctx);

}  // namespace zolver
