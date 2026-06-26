#pragma once

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <unordered_map>
#include <optional>

namespace xolver {

// Structural-integer probe for mgc-class SAT cases.
//
// The mgc benchmark family (Sturm/RedLog 2016) has the form:
//   "all variables positive, find a model of a polynomial system"
// z3-nlsat closes mgc_09/10 in ~0.13s with 2 decisions, which the
// trace reveals as small-integer guesses for the highest-exponent
// variables (e.g. vv3=2 in mgc_09, where vv3^9 appears).
//
// This probe is a poor-man's nlsat front-end: enumerate small
// integer/dyadic candidates for the top-K high-exponent variables,
// fill the remaining vars with a heuristic default (1), and validate
// the candidate via the exact kernel sign check.
//
// Sound: invariant 1 (validateCandidate over all active constraints).
// Incomplete: won't catch cases needing non-trivial rationals for
// non-structural vars. Cheap and harmless when it doesn't fire.
//
// Gated by env var XOLVER_NRA_INT_PROBE (default OFF).
class StructuralIntegerProbe {
public:
    struct Constraint {
        PolyId poly;
        Relation rel;
    };

    // Returns a kernel-validated rational model if found; nullopt otherwise.
    static std::optional<std::unordered_map<VarId, mpq_class>> tryProbe(
        const std::vector<Constraint>& constraints,
        PolynomialKernel& kernel,
        int maxStructuralVars = 3,
        int maxBudget = 2048);

    // Equality-cascade SAT solver (mgc-class "assign the high-degree generator
    // variables first" strategy). A *generator* is a variable that appears with
    // degree >= 2 in some equality (it cannot be solved linearly). Pinning the
    // generators to concrete values turns every high-degree monomial (e.g.
    // vv3^16) into a number, collapsing each residual equality to LINEAR in one
    // remaining variable; propagateForcedBindings then derives the rest of the
    // model by substitute + positive-factor divide + degree-1 solve to fixpoint.
    // The full point is validated by the exact kernel sign over ALL original
    // constraints (invariant 1) — purely rational, NEVER libpoly root isolation,
    // so it is immune to the libpoly multivariate-isolation heap bug. Sound: a
    // validated rational point is SAT; absence of one ⇒ caller stays Unknown
    // (this is a SAT finder, never emits UNSAT).
    //
    // Closes mgc_09/mgc_10 (degree-16/18 SAT) where CDCAC times out projecting
    // the high-degree atom. Gated by XOLVER_NRA_EQ_CASCADE (default OFF).
    static std::optional<std::unordered_map<VarId, mpq_class>> trySolveCascade(
        const std::vector<Constraint>& constraints,
        PolynomialKernel& kernel,
        int maxBudget = 500000);
};

} // namespace xolver
