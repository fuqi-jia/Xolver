// Equality-cascade SAT solver (StructuralIntegerProbe::trySolveCascade).
//
// The mgc-class strategy: assign the high-degree "generator" variables (degree
// >= 2, which cannot be solved linearly), which collapses every high-degree
// monomial to a number and turns each residual equality linear in one remaining
// variable; derive those, then validate the full point exactly. Pure rational —
// never libpoly root isolation.

#include <doctest/doctest.h>
#include "theory/arith/nra/StructuralIntegerProbe.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>

using namespace xolver;

namespace {
using C = StructuralIntegerProbe::Constraint;
}

TEST_CASE("eq-cascade: x^2-4=0, x*y-6=0, x>0, y>0 => x=2, y=3") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");

    // x is the generator (degree 2); once pinned, x*y-6 is linear in y.
    PolyId x2m4 = kernel->add(kernel->pow(kernel->mkVar(x), 2), kernel->mkConst(mpq_class(-4)));
    PolyId xym6 = kernel->add(kernel->mul(kernel->mkVar(x), kernel->mkVar(y)),
                              kernel->mkConst(mpq_class(-6)));
    std::vector<C> cons = {
        {x2m4, Relation::Eq},
        {xym6, Relation::Eq},
        {kernel->neg(kernel->mkVar(x)), Relation::Lt},   // -x < 0  ⇒ x > 0
        {kernel->neg(kernel->mkVar(y)), Relation::Lt},   // -y < 0  ⇒ y > 0
    };

    auto model = StructuralIntegerProbe::trySolveCascade(cons, *kernel);
    REQUIRE(model.has_value());
    CHECK(model->at(x) == mpq_class(2));
    CHECK(model->at(y) == mpq_class(3));
}

TEST_CASE("eq-cascade: needs a dyadic generator value (2*a-1=0 style)") {
    auto kernel = createPolynomialKernel();
    VarId a = kernel->getOrCreateVar("a");
    VarId b = kernel->getOrCreateVar("b");

    // a^2 appears (generator, degree 2). Satisfied at a = 1/2: 4*a^2 - 1 = 0.
    // Then 2*a*b - 1 = 0 ⇒ b = 1. Forces the dyadic ladder (a = 1/2).
    PolyId c1 = kernel->add(kernel->mul(kernel->mkConst(mpq_class(4)),
                                        kernel->pow(kernel->mkVar(a), 2)),
                            kernel->mkConst(mpq_class(-1)));            // 4a^2 - 1
    PolyId c2 = kernel->add(kernel->mul(kernel->mul(kernel->mkConst(mpq_class(2)),
                                                    kernel->mkVar(a)),
                                        kernel->mkVar(b)),
                            kernel->mkConst(mpq_class(-1)));            // 2ab - 1
    std::vector<C> cons = {
        {c1, Relation::Eq},
        {c2, Relation::Eq},
        {kernel->neg(kernel->mkVar(a)), Relation::Lt},
        {kernel->neg(kernel->mkVar(b)), Relation::Lt},
    };

    auto model = StructuralIntegerProbe::trySolveCascade(cons, *kernel);
    REQUIRE(model.has_value());
    CHECK(model->at(a) == mpq_class(1, 2));
    CHECK(model->at(b) == mpq_class(1));
}

TEST_CASE("eq-cascade: unsatisfiable positive system => no model (never UNSAT)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    // x^2 + 1 = 0 has no positive (no real) root: cascade must return nullopt,
    // never a (false) model. (UNSAT is not this engine's job.)
    PolyId p = kernel->add(kernel->pow(kernel->mkVar(x), 2), kernel->mkConst(mpq_class(1)));
    std::vector<C> cons = {
        {p, Relation::Eq},
        {kernel->neg(kernel->mkVar(x)), Relation::Lt},
    };
    auto model = StructuralIntegerProbe::trySolveCascade(cons, *kernel);
    CHECK_FALSE(model.has_value());
}
