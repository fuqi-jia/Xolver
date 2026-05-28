#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/GcdDivisibilityReasoner.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }
static PolyId var(PolynomialKernel& k, const char* n) { return k.mkVar(k.getOrCreateVar(n)); }
static PolyId cst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }
static PolyId scaled(PolynomialKernel& k, long c, PolyId p) { return k.mul(cst(k, c), p); }

// 2x + 4y - 3 = 0 : gcd(2,4)=2, 2 ∤ 3  => no integer solution => UNSAT
TEST_CASE("Gcd: 2x + 4y - 3 = 0 -> Conflict") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId p = kernel->sub(kernel->add(scaled(*kernel, 2, var(*kernel, "x")),
                                       scaled(*kernel, 4, var(*kernel, "y"))),
                           cst(*kernel, 3));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// nonlinear monomial: 2*x*y + 4*z - 3 = 0 -> UNSAT (parity on the product term)
TEST_CASE("Gcd: 2xy + 4z - 3 = 0 -> Conflict (nonlinear monomial)") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId xy = kernel->mul(var(*kernel, "x"), var(*kernel, "y"));
    PolyId p = kernel->sub(kernel->add(scaled(*kernel, 2, xy),
                                       scaled(*kernel, 4, var(*kernel, "z"))),
                           cst(*kernel, 3));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// 2x + 4y - 6 = 0 : gcd=2 | 6 => satisfiable (x=1,y=1) => must NOT refute
TEST_CASE("Gcd: 2x + 4y - 6 = 0 -> NoChange (divisible, satisfiable)") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId p = kernel->sub(kernel->add(scaled(*kernel, 2, var(*kernel, "x")),
                                       scaled(*kernel, 4, var(*kernel, "y"))),
                           cst(*kernel, 6));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// gcd(3,5)=1 divides everything => NoChange
TEST_CASE("Gcd: 3x + 5y - 7 = 0 -> NoChange (gcd 1)") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId p = kernel->sub(kernel->add(scaled(*kernel, 3, var(*kernel, "x")),
                                       scaled(*kernel, 5, var(*kernel, "y"))),
                           cst(*kernel, 7));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Inequalities have slack; gcd cannot refute them => NoChange (soundness guard).
TEST_CASE("Gcd: 2x + 4y - 3 <= 0 -> NoChange (inequality)") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId p = kernel->sub(kernel->add(scaled(*kernel, 2, var(*kernel, "x")),
                                       scaled(*kernel, 4, var(*kernel, "y"))),
                           cst(*kernel, 3));
    auto res = r.run({{p, Relation::Leq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Pure constant equality (no monomials) is left to the trivial-constant stage.
TEST_CASE("Gcd: 5 = 0 -> NoChange (no monomials, g=0)") {
    auto kernel = createPolynomialKernel();
    GcdDivisibilityReasoner r(*kernel);
    PolyId p = cst(*kernel, 5);
    auto res = r.run({{p, Relation::Eq, mkReason(1)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}
