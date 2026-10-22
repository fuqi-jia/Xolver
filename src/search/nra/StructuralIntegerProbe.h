#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include "ir/types.h"
#include <gmpxx.h>
#include <vector>
#include <unordered_map>
#include <optional>

namespace xolver {

// Rational equality-cascade candidate search with exact model validation.
class StructuralIntegerProbe {
public:
    struct Constraint {
        PolyId poly;
        Relation rel;
    };

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
    // the high-degree atom.
    static std::optional<std::unordered_map<VarId, mpq_class>> trySolveCascade(
        const std::vector<Constraint>& constraints,
        PolynomialKernel& kernel,
        int maxBudget = 500000);
};

} // namespace xolver
