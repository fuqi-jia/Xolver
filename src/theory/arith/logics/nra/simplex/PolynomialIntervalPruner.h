#pragma once

// OSF-CDCAC P7: polynomial interval pruning.
//
// Given the active NRA constraint set and the CertifiedSimplexFacts
// (bounds, equalities), derive a conservative interval [L, U] for each
// constraint polynomial. If the interval contradicts the relation
// (e.g. constraint p = 0 but L > 0), emit a sound theory conflict
// whose reasons union the variable-bound reasons that justified the
// interval.
//
// Soundness model:
//   The interval is computed via monomial-wise interval arithmetic --
//   each monomial m = c * x^a * y^b * ... gets an interval from the
//   sign/bound info of x, y, ..., and the polynomial interval is the
//   sum (Minkowski-style). If the resulting [L, U] interval excludes
//   the value zero relative to the relation, we have a proof of UNSAT.
//
//   The reasons attached to the conflict are the union of:
//   - the constraint's own reason
//   - the CertifiedBound reasons for every variable whose interval
//     contributed to the contradiction
//
// Per the spec § 6:
//   For atom p <= 0:
//      if L > 0: contradiction
//      if U <= 0: certified true
//   For atom p >= 0:
//      if U < 0: contradiction
//      if L >= 0: certified true
//   For atom p = 0:
//      if 0 not in [L,U]: contradiction
//
// This pruner runs as an early NRA stage (XOLVER_NRA_OSF_PRUNE,
// default OFF). On contradiction returns a Conflict; otherwise nullopt
// (continue to next stage). Never emits a SAT verdict directly.

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/simplex/CertifiedSimplexFacts.h"
#include "expr/types.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {

struct IntervalConstraint {
    PolyId poly;
    Relation rel;     // p rel 0
    SatLit reason;
};

struct IntervalConflict {
    std::vector<SatLit> reasons;   // SAT literals to refute; union of constraint + bound reasons
    std::string explanation;       // human-readable for diagnostics
};

// Returns Conflict if at least one constraint's interval contradicts its
// relation. nullopt otherwise (no conclusion -- caller continues to next
// stage).
std::optional<IntervalConflict> tryRefuteByPolynomialInterval(
    const std::vector<IntervalConstraint>& constraints,
    const CertifiedSimplexFacts& facts,
    PolynomialKernel& kernel);

// Iterative refutation with polynomial factoring + bound back-propagation.
// On each round:
//   1. Factor each EQ constraint by sign-definite common-factor variables.
//      For `p = 0` where p = v^k * q and v has sign != 0 (definite),
//      add `q = 0` to the working constraint set (sound: v != 0 + v*q = 0
//      => q = 0).
//   2. Back-propagate: for each EQ constraint where one variable can be
//      solved for, derive its interval from the other terms.
//   3. Re-run polynomial interval pruning.
// Returns the first conflict found (with reason union) or nullopt at fixpoint.
std::optional<IntervalConflict> tryRefuteByIterativeFactoring(
    const std::vector<IntervalConstraint>& constraints,
    CertifiedSimplexFacts& facts,    // mutated as bounds tighten
    PolynomialKernel& kernel,
    int maxIterations = 6);

// Helper: compute the interval of a single monomial `c * prod(x^e)` given
// certified bounds for the variables. Returns nullopt for any side that
// can't be bounded (e.g. variable is unbounded above and the exponent is
// odd). Reasons collected into `usedReasons`.
struct MonomialInterval {
    std::optional<mpq_class> low;
    std::optional<mpq_class> high;
    bool valid = true;
};
MonomialInterval intervalOfMonomial(
    const mpq_class& coefficient,
    const std::vector<std::pair<VarId, int>>& powers,
    const CertifiedSimplexFacts& facts,
    std::vector<SatLit>& usedReasons);

} // namespace xolver
