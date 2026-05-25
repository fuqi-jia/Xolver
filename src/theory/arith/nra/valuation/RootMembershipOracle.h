#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"
#include "expr/types.h"
#include <gmpxx.h>

namespace nlcolver {

// Exact root-membership oracle (LAZARD.md step 4). Decides whether the real
// algebraic number beta — a real root of the rational polynomial `defPoly`,
// isolated in the interval [betaLo, betaHi] (a point if betaLo==betaHi) — is a
// root of F at the REAL embedding of the tower K = ctx.
//
// F is a RationalPolynomial in the tower extension variables + targetVar (a
// univariate in targetVar with tower-element coefficients). Three-state, with
// the hard soundness rule that Unknown is NEVER Drop:
//   Keep    = EXACT proof F(beta) = 0 at the embedding
//   Drop    = EXACT proof F(beta) != 0 at the embedding
//   Unknown = inconclusive (no interval-overlap heuristic proves Keep/Drop; no
//             rational-Norm-only criterion decides branch membership)
//
// Decision (all exact except where it yields Unknown):
//   (0) rational beta: substitute + tower zero-test.
//   (1) interval fast-DROP: F(alpha,beta) box-interval excludes 0.
//   (2) G = gcd_K(F, squarefree(defPoly)); G constant -> Drop; deg G == deg sf
//       -> Keep (sf | F, so every root of sf incl. beta is a root of F).
//   (3) G linear -> its root is a tower element c (a root of sf); decide beta==c
//       by interval refinement + Sturm root count (same single root of sf).
//   else -> Unknown (higher-degree proper factor needs Trager factorization).
enum class RootMembership { Keep, Drop, Unknown };

RootMembership lazardRootMembership(const RationalPolynomial& F, VarId targetVar,
                                    const RationalPolynomial& defPoly,
                                    const mpq_class& betaLo, const mpq_class& betaHi,
                                    const TowerContext& ctx);

}  // namespace nlcolver
