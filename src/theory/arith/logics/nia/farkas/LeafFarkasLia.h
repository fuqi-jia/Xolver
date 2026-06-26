#pragma once

// Farkas-ranking leaf refutation by COST-VAR EXISTENTIAL ELIMINATION + LIA.
//
// For the VeryMax/Stroeder ranking-synthesis class, after the bounded template
// coeffs B are fixed, B·λ is linear and the ONLY residual nonlinearity is the
// cost-multiplier product CT·λ, where CT is an UNBOUNDED existential integer.
// Such a CT must be ELIMINATED, not branched (research note 2026-06-07):
//
//     ∃CT∈ℤ.  A(λ) + CT·S(λ)  ⋈ 0     (⋈ ∈ {>, ≥})
//       ≡   S(λ) ≠ 0   ∨   A(λ) ⋈ 0
//
// (S≠0 ⇒ push CT to ±∞ to satisfy ⋈; S=0 ⇒ CT vanishes, A⋈0 remains.) This
// removes the CT·λ multiplication outright, leaving a DISJUNCTION of pure-LIA
// systems in λ. The leaf is UNSAT iff every disjunct is integer-LIA-infeasible
// — discharged exactly by the integer MILP engine (simplex + B&B + cuts). No
// relaxation, no CAD, no polynomial blow-up.
//
// Isolated TU: pulls InternalMilpEngine (→ GeneralSimplex.h / xolver::BoundInfo),
// which ODR-clashes with the linearizer's BoundInfo in NiaSolver.cpp's graph.

#include "theory/arith/logics/nra/core/CdcacCommon.h"     // ConstraintId, ModelSeed
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "expr/types.h"
#include <unordered_set>
#include <vector>

namespace xolver {

class PolynomialKernel;

// Prove a B-fixed Farkas leaf integer-infeasible by eliminating every unbounded
// cost var in `ctVars` (each must occur only in a single strict/non-strict
// inequality, linearly) and discharging the resulting pure-LIA disjunction.
// Returns true iff PROVEN UNSAT. Bails (false) on any shape it does not handle
// (a CT in an equality, a CT shared across constraints, or a non-{const,λ,CT·λ}
// monomial) — the caller then falls back to its real-relaxation leaf engine.
bool niaLeafFarkasLiaUnsat(const std::vector<CdcacConstraint>& cons,
                           const std::unordered_set<VarId>& ctVars,
                           PolynomialKernel& kernel);

} // namespace xolver
