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
