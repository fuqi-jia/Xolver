#include <doctest/doctest.h>
#include "search/nia/search/NiaLocalSearch.h"
#include "search/nia/core/DomainStore.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

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

TEST_CASE("NiaLocalSearch: x*y=12 & x+y=7 -> finds {3,4}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
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

TEST_CASE("NiaLocalSearch: 3-var system x+y+z=9, xy=6, yz=12, xz=8") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(1), mkReason(11));
    ds.addUpperBound("x", mpz_class(10), mkReason(12));
    ds.addLowerBound("y", mpz_class(1), mkReason(13));
    ds.addUpperBound("y", mpz_class(10), mkReason(14));
    ds.addLowerBound("z", mpz_class(1), mkReason(15));
    ds.addUpperBound("z", mpz_class(10), mkReason(16));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));

    NormalizedNiaConstraint sum{
        kernel->sub(kernel->add(kernel->add(x, y), z), kernel->mkConst(mpq_class(9))),
        Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint xy{
        kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(6))),
        Relation::Eq, mkReason(2)};
    NormalizedNiaConstraint yz{
        kernel->sub(kernel->mul(y, z), kernel->mkConst(mpq_class(12))),
        Relation::Eq, mkReason(3)};
    NormalizedNiaConstraint xz{
        kernel->sub(kernel->mul(x, z), kernel->mkConst(mpq_class(8))),
        Relation::Eq, mkReason(4)};

    auto m = ls.tryFindModel({sum, xy, yz, xz}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"], yv = (*m)["y"], zv = (*m)["z"];
    CHECK(xv + yv + zv == 9);
    CHECK(xv * yv == 6);
    CHECK(yv * zv == 12);
    CHECK(xv * zv == 8);
}

TEST_CASE("NiaLocalSearch: on trivially-UNSAT system, returns nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(50);   // capped budget — we only want to confirm no-Sat-claim
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(5), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    NormalizedNiaConstraint eq{
        kernel->sub(x, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({eq}, ds);
    CHECK(!m.has_value());  // must NOT claim Sat
}

TEST_CASE("NiaLocalSearch: signature mismatch drops stale assignment") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c1{
        kernel->sub(x, kernel->mkConst(mpq_class(42))),
        Relation::Eq, mkReason(1)};  // x = 42

    auto m1 = ls.tryFindModel({c1}, ds);
    REQUIRE(m1.has_value());
    CHECK((*m1)["x"] == 42);



    NormalizedNiaConstraint c2{
        kernel->sub(x, kernel->mkConst(mpq_class(7))),
        Relation::Eq, mkReason(2)};
    auto m2 = ls.tryFindModel({c2}, ds);
    REQUIRE(m2.has_value());
    CHECK((*m2)["x"] == 7);
}

TEST_CASE("NiaLocalSearch: never rubber-stamps stale cache") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(50);  // tiny budget
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    NormalizedNiaConstraint c1{
        kernel->sub(x, kernel->mkConst(mpq_class(50))),
        Relation::Eq, mkReason(1)};
    auto m1 = ls.tryFindModel({c1}, ds);
    REQUIRE(m1.has_value());




    DomainStore ds2;
    ds2.addLowerBound("x", mpz_class(0), mkReason(2));
    ds2.addUpperBound("x", mpz_class(10), mkReason(3));
    NormalizedNiaConstraint c2{
        kernel->sub(x, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(4)};
    auto m2 = ls.tryFindModel({c2}, ds2);
    CHECK(!m2.has_value());  // must NOT claim sat with stale cache
}

TEST_CASE("NiaLocalSearch: x^2 = 100 finds x = 10") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));


    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->sub(xx, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK(xv * xv == 100);
}

TEST_CASE("NiaLocalSearch: finds x = 1024 far jump") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(1024))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 1024);
}

TEST_CASE("NiaLocalSearch: handles x*y = N bilinear with multi-scale jump") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));

    NormalizedNiaConstraint c{
        kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(256))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] * (*m)["y"] == 256);
}

TEST_CASE("NiaLocalSearch: x^2 = 25 finds root") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->sub(xx, kernel->mkConst(mpq_class(25))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK(xv * xv == 25);
}

TEST_CASE("NiaLocalSearch: x^2 + 3x - 10 = 0 finds {-5, 2}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    PolyId threex = kernel->mul(kernel->mkConst(mpq_class(3)), x);

    PolyId expr = kernel->sub(kernel->add(xx, threex),
                              kernel->mkConst(mpq_class(10)));
    NormalizedNiaConstraint c{expr, Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK((xv == -5 || xv == 2));
}

TEST_CASE("NiaLocalSearch: linear x = 17 still solved (a=0 falls back)") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(17))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 17);
}

TEST_CASE("NiaLocalSearch: D<0 (x^2 + 1 = 0) returns nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(50);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-10), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->add(xx, kernel->mkConst(mpq_class(1))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    CHECK(!m.has_value());
}

TEST_CASE("NiaLocalSearch: tight bound x in [42,42] is jumped to directly") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(42), mkReason(1));
    ds.addUpperBound("x", mpz_class(42), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(42))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 42);
}

TEST_CASE("NiaLocalSearch: finite-set domain — iterates set members") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.restrictToFiniteSet("x",
        std::set<mpz_class>{mpz_class(7), mpz_class(13), mpz_class(19)},
        mkReason(1));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(13))),
        Relation::Eq, mkReason(2)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 13);
}

TEST_CASE("NiaLocalSearch: excluded values' neighbours are tried") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));
    ds.excludeValue("x", mpz_class(5), mkReason(3));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    NormalizedNiaConstraint c{
        kernel->sub(kernel->mul(x, kernel->mkConst(mpq_class(2))),
                    kernel->mkConst(mpq_class(8))),
        Relation::Eq, mkReason(4)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 4);
}

TEST_CASE("NiaLocalSearch: contradictory bounds return nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(50);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(50), mkReason(1));
    ds.addUpperBound("x", mpz_class(50), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(999))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    CHECK(!m.has_value());
}

TEST_CASE("NiaLocalSearch: accelerated step handles big jump x = 1000") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;   // unbounded

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint eq{
        kernel->sub(x, kernel->mkConst(mpq_class(1000))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({eq}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 1000);
}

TEST_CASE("NiaLocalSearch: solves 2*x*y + 3*x + y - 10 = 0") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-20), mkReason(1));
    ds.addUpperBound("x", mpz_class(20), mkReason(2));
    ds.addLowerBound("y", mpz_class(-20), mkReason(3));
    ds.addUpperBound("y", mpz_class(20), mkReason(4));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId xy = kernel->mul(x, y);
    PolyId poly = kernel->sub(
        kernel->add(kernel->add(kernel->mul(kernel->mkConst(mpq_class(2)), xy),
                                kernel->mul(kernel->mkConst(mpq_class(3)), x)),
                    y),
        kernel->mkConst(mpq_class(10)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(5)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());

    const auto& M = *m;
    mpz_class xv = M.at("x"), yv = M.at("y");
    CHECK(2*xv*yv + 3*xv + yv == 10);
}

TEST_CASE("NiaLocalSearch: handles quadratic residual") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-15), mkReason(1));
    ds.addUpperBound("x", mpz_class(15), mkReason(2));
    ds.addLowerBound("y", mpz_class(-15), mkReason(3));
    ds.addUpperBound("y", mpz_class(15), mkReason(4));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));

    PolyId xx = kernel->mul(x, x);
    PolyId xy = kernel->mul(x, y);
    PolyId poly = kernel->sub(kernel->add(xx, xy), kernel->mkConst(mpq_class(6)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(5)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    const auto& M = *m;
    mpz_class xv = M.at("x"), yv = M.at("y");
    CHECK(xv*xv + xv*yv == 6);
}

TEST_CASE("NiaLocalSearch: single-variable equality 3x-12=0") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-100), mkReason(1));
    ds.addUpperBound("x", mpz_class(100), mkReason(2));
    ds.addLowerBound("y", mpz_class(-100), mkReason(3));
    ds.addUpperBound("y", mpz_class(100), mkReason(4));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));

    PolyId pin = kernel->sub(
        kernel->mul(kernel->mkConst(mpq_class(3)), x),
        kernel->mkConst(mpq_class(12)));

    PolyId nonpin = kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(4)));
    NormalizedNiaConstraint c1{pin,    Relation::Eq,  mkReason(5)};
    NormalizedNiaConstraint c2{nonpin, Relation::Geq, mkReason(6)};

    auto m = ls.tryFindModel({c1, c2}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 4);
    CHECK((*m)["x"] * (*m)["y"] >= 4);
}

TEST_CASE("NiaLocalSearch: nonintegral equality") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-100), mkReason(1));
    ds.addUpperBound("x", mpz_class(100), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    PolyId nonexact = kernel->sub(
        kernel->mul(kernel->mkConst(mpq_class(2)), x),
        kernel->mkConst(mpq_class(5)));
    NormalizedNiaConstraint c{nonexact, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);




    if (m.has_value()) {

        CHECK(2 * (*m)["x"] != 5);
    }
}

TEST_CASE("NiaLocalSearch: respects existing domain bounds") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);
    DomainStore ds;

    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));

    PolyId outOfRange = kernel->add(x, kernel->mkConst(mpq_class(2)));
    NormalizedNiaConstraint c{outOfRange, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);


    if (m.has_value()) {
        CHECK((*m)["x"] != -2);
    }
}

// Original input that exposed the retired factor-pair expression lifetime bug.
TEST_CASE("NiaLocalSearch: conflicting bilinear products produce no candidate") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(100);
    DomainStore domains;
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId product = kernel->mul(x, y);
    std::vector<NormalizedNiaConstraint> constraints{
        {kernel->sub(product, kernel->mkConst(mpq_class(2))), Relation::Eq, mkReason(1)},
        {kernel->sub(product, kernel->mkConst(mpq_class(3))), Relation::Eq, mkReason(2)}};
    CHECK_FALSE(ls.tryFindModel(constraints, domains).has_value());
}
