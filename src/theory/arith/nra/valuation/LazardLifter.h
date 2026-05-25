#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"   // TowerContext
#include "expr/types.h"
#include <gmpxx.h>
#include <utility>
#include <vector>

namespace nlcolver {

// ---------------------------------------------------------------------------
// LazardLifter — real-root placement for one CDCAC lift (LAZARD.md step D).
//
// Given the level-k polynomials (each a RationalPolynomial in the tower
// extension variables + mainVar) and a prefix tower sample described by `ctx`
// (the lower coordinates x_0..x_{k-1} as the tower generators alpha_i), produce
// the ordered real-root SECTIONS of those polynomials at the real embedding,
// from which the caller builds the section/sector cell decomposition.
//
// SOUNDNESS: built entirely on the exact root-membership oracle, which is sound
// even on a reducible tower (RootMembershipOracle.h). `supported == false`
// whenever any step is inconclusive (Norm budget/degeneracy, non-exact
// squarefree, or any candidate the oracle returns Unknown for) — the caller then
// falls back (Collins) or returns Unknown. NEVER UNSAT from an unsupported lift.
// ---------------------------------------------------------------------------

// A real-root section in the mainVar axis: an algebraic number isolated by
// [lo,hi] over the shared rational defining poly LazardLiftResult::defPoly
// (lo==hi for an exact rational section point).
struct LazardSection {
    mpq_class lo, hi;
    bool isPoint() const { return lo == hi; }
};

struct LazardLiftResult {
    bool supported = false;
    RationalPolynomial defPoly;            // shared Q defining poly of all sections
    std::vector<LazardSection> sections;   // ascending, disjoint; ALL real roots at the embedding
};

// Increment 1 — per-polynomial placement. Each poly is isolated over its OWN
// Norm via isolateRealRootsInTower (the oracle's gcd-Keep needs the candidate's
// minimal rational defPoly, so per-poly Norms — not a combined product). Roots
// are placed only when exactly ONE poly contributes boundaries at this level; a
// genuine cross-poly merge (needs Q-factorization/Trager) returns unsupported.
//   contributors == 0 => supported, empty sections (single (-inf,+inf) sector)
//   contributors == 1 => supported, that poly's kept roots over defPoly
//   contributors >= 2 => unsupported (caller falls back to Collins / Unknown)
LazardLiftResult lazardLift(const std::vector<RationalPolynomial>& polys,
                            VarId mainVar, const TowerContext& ctx);

}  // namespace nlcolver
