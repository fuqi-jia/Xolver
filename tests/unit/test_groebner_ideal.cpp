#include <cstdlib>
#include <doctest/doctest.h>
#include "theory/arith/logics/nia/reasoners/GroebnerIdealReasoner.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }
static PolyId var(PolynomialKernel& k, const char* n) { return k.mkVar(k.getOrCreateVar(n)); }
static PolyId cst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }

// {x*y - 1 = 0, x = 0}: x=0 forces 0 = 1 -> no common root (1 in ideal) -> UNSAT.
TEST_CASE("Groebner: xy-1=0 & x=0 -> Conflict (1 in ideal)") {
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId xy1 = kernel->sub(kernel->mul(var(*kernel, "x"), var(*kernel, "y")), cst(*kernel, 1));
    PolyId x   = var(*kernel, "x");
    auto res = r.run({{xy1, Relation::Eq, mkReason(1)}, {x, Relation::Eq, mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// Linear-inconsistent: {x+y-1=0, x+y-2=0}: difference is 1 -> 1 in ideal -> UNSAT.
TEST_CASE("Groebner: x+y-1=0 & x+y-2=0 -> Conflict") {
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId xpy = kernel->add(var(*kernel, "x"), var(*kernel, "y"));
    PolyId c1 = kernel->sub(xpy, cst(*kernel, 1));
    PolyId c2 = kernel->sub(xpy, cst(*kernel, 2));
    auto res = r.run({{c1, Relation::Eq, mkReason(1)}, {c2, Relation::Eq, mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// {x*y - 1 = 0, x - 2 = 0}: x=2 -> 2y=1 has a complex/rational root -> 1 NOT in
// ideal. Integer-infeasibility (2y=1) is GCD's job, NOT Groebner's. Must NOT refute.
TEST_CASE("Groebner: xy-1=0 & x-2=0 -> NoChange (has complex root)") {
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId xy1 = kernel->sub(kernel->mul(var(*kernel, "x"), var(*kernel, "y")), cst(*kernel, 1));
    PolyId x2  = kernel->sub(var(*kernel, "x"), cst(*kernel, 2));
    auto res = r.run({{xy1, Relation::Eq, mkReason(1)}, {x2, Relation::Eq, mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Single satisfiable equality -> NoChange.
TEST_CASE("Groebner: x+y-3=0 -> NoChange (satisfiable)") {
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId c1 = kernel->sub(kernel->add(var(*kernel, "x"), var(*kernel, "y")), cst(*kernel, 3));
    auto res = r.run({{c1, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// x^2 - 2 = 0: has real roots (±sqrt2) -> 1 NOT in ideal -> NoChange (integer
// infeasibility is modular/RRT's job, not Groebner's).
TEST_CASE("Groebner: x^2-2=0 -> NoChange (real roots exist)") {
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId xx2 = kernel->sub(kernel->mul(var(*kernel, "x"), var(*kernel, "x")), cst(*kernel, 2));
    auto res = r.run({{xx2, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// iter-86: soundness boundary test for iter-82 env-overridable size guard.
// Relaxing XOLVER_NIA_GROBNER_MAX_EQ / _MAX_VARS must not produce wrong
// verdict on a SATISFIABLE system. The reasoner is allowed to return
// Conflict (1 in ideal) OR NoChange, never anything else.
TEST_CASE("Groebner: relaxed env caps preserve NoChange on satisfiable system") {
    // x*y = 6 ∧ x + y = 5 → ℂ-roots (2,3) and (3,2). 1 NOT in ideal.
    setenv("XOLVER_NIA_GROBNER_MAX_EQ", "50", 1);
    setenv("XOLVER_NIA_GROBNER_MAX_VARS", "30", 1);
    auto kernel = createPolynomialKernel();
    GroebnerIdealReasoner r(*kernel);
    PolyId xy6  = kernel->sub(kernel->mul(var(*kernel, "x"), var(*kernel, "y")), cst(*kernel, 6));
    PolyId xpy5 = kernel->sub(kernel->add(var(*kernel, "x"), var(*kernel, "y")), cst(*kernel, 5));
    auto res = r.run({{xy6, Relation::Eq, mkReason(1)},
                      {xpy5, Relation::Eq, mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
    // Defensive: NEVER Conflict on a system with complex roots.
    CHECK(res.kind != NiaReasoningKind::Conflict);
}
