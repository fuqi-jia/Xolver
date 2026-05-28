#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/SquareBoundReasoner.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// Build a normalized constraint for a*x^2 + b*x + c rel 0
static NormalizedNiaConstraint makeSquareConstraint(
    PolynomialKernel& kernel, const std::string& var,
    const mpz_class& a, const mpz_class& b, const mpz_class& c,
    Relation rel, SatLit reason) {

    PolyId varPoly = kernel.mkVar(kernel.getOrCreateVar(var));
    PolyId aPoly = kernel.mkConst(mpq_class(a));
    PolyId bPoly = kernel.mkConst(mpq_class(b));
    PolyId cPoly = kernel.mkConst(mpq_class(c));

    PolyId x2 = kernel.pow(varPoly, 2);
    PolyId ax2 = kernel.mul(aPoly, x2);
    PolyId bx = kernel.mul(bPoly, varPoly);
    PolyId poly = kernel.add(ax2, kernel.add(bx, cPoly));

    return {poly, rel, reason};
}

TEST_CASE("SquareBound: x^2 - 4 <= 0 -> bounds [-2, 2]") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    // x^2 - 4 <= 0  =>  a=1, b=0, c=-4
    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-4),
                                  Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasLower);
    CHECK(d->hasUpper);
    CHECK(d->lower.value == -2);
    CHECK(d->upper.value == 2);
}

TEST_CASE("SquareBound: x^2 + 1 <= 0 -> UNSAT (c=1, -c=-1 < 0)") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    // x^2 + 1 <= 0  =>  a=1, b=0, c=1
    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(1),
                                  Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("SquareBound: x^2 - 49 = 0 -> finite set {-7, 7}") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-49),
                                  Relation::Eq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    REQUIRE(d->finiteValues.has_value());
    CHECK(d->finiteValues->size() == 2);
    CHECK(d->finiteValues->count(mpz_class(7)));
    CHECK(d->finiteValues->count(mpz_class(-7)));
}

TEST_CASE("SquareBound: x^2 - 50 = 0 -> UNSAT (not perfect square)") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-50),
                                  Relation::Eq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("SquareBound: x^2 = 0 -> finite set {0}") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(0),
                                  Relation::Eq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    REQUIRE(d->finiteValues.has_value());
    CHECK(d->finiteValues->size() == 1);
    CHECK(*d->finiteValues->begin() == 0);
}

TEST_CASE("SquareBound: x^2 - 4 != 0 -> exclusions {2, -2}") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-4),
                                  Relation::Neq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->excludedValues.count(mpz_class(2)));
    CHECK(d->excludedValues.count(mpz_class(-2)));
}

TEST_CASE("SquareBound: x^2 != 0 -> exclusion {0}") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(0),
                                  Relation::Neq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->excludedValues.count(mpz_class(0)));
}

TEST_CASE("SquareBound: x^2 - 3 != 0 -> NoChange (tautology, 3 not square)") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-3),
                                  Relation::Neq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SquareBound: x^2 - 4 >= 0 -> NoChange (deferred)") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSquareConstraint(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-4),
                                  Relation::Geq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SquareBound: linear constraint ignored") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    PolyId varPoly = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId poly = kernel->add(kernel->mul(two, varPoly), kernel->mkConst(mpq_class(5)));

    auto c = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(1)};
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SquareBound: multivariate ignored") {
    auto kernel = createPolynomialKernel();
    SquareBoundReasoner reasoner(*kernel);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId poly = kernel->add(kernel->pow(x, 2), kernel->pow(y, 2));

    auto c = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(1)};
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}
