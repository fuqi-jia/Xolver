#include <doctest/doctest.h>
#include "theory/arith/nia/search/NiaLocalSearch.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// The per-call time cap must not break finding an easy SAT model. x^2 - 4 = 0
// with x in [0,5] has the model x = 2; local search must still return it.
TEST_CASE("NiaLocalSearch: finds easy model x^2-4=0, x in [0,5] (cap intact)") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(4)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 2);
}

// Even with the default budget, an easy model is found (budget is generous
// relative to a tiny search). Also verifies setBudgetMs unlimited path.
TEST_CASE("NiaLocalSearch: unlimited budget still finds the easy model") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);   // unlimited
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(4)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 2);
}

// Enhanced WalkSAT (XOLVER_NIA_LOCALSEARCH) finds a model the basic ±[-3,3]
// sweep misses: x*y = 12 and x + y = 7 have model {3,4}/{4,3}, with a
// coordinate (4) outside the basic 2-var window. The accelerated critical move
// jumps there. (Candidate-only; soundness is the caller's validator, so the
// returned model must satisfy both constraints.)
TEST_CASE("NiaLocalSearch enhanced: x*y=12 & x+y=7 -> finds {3,4}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setBudgetMs(0);  // unlimited for the test
    DomainStore ds;     // unbounded vars

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    NormalizedNiaConstraint prod{kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(12))),
                                 Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint sum{kernel->sub(kernel->add(x, y), kernel->mkConst(mpq_class(7))),
                                Relation::Eq, mkReason(2)};

    auto m = ls.tryFindModel({prod, sum}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"], yv = (*m)["y"];
    CHECK(xv * yv == 12);
    CHECK(xv + yv == 7);
}
