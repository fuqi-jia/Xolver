#include <doctest/doctest.h>
#include "theory/arith/logics/nia/core/LinearNiaDomainReasoner.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// Helper: build a polynomial a*var + c and return NormalizedNiaConstraint
static NormalizedNiaConstraint makeLinearConstraint(
    PolynomialKernel& kernel, const std::string& var,
    const mpz_class& a, const mpz_class& c, Relation rel, SatLit reason) {

    PolyId varPoly = kernel.mkVar(kernel.getOrCreateVar(var));
    PolyId aPoly = kernel.mkConst(mpq_class(a));
    PolyId cPoly = kernel.mkConst(mpq_class(c));
    PolyId ax = kernel.mul(aPoly, varPoly);
    PolyId poly = kernel.add(ax, cPoly); // a*x + c
    return {poly, rel, reason};
}

TEST_CASE("LinearNiaDomain: positive coeff Leq 2x+5<=0 -> x<=-3") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(2), mpz_class(5), Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasUpper);
    CHECK(d->upper.value == -3);
}

TEST_CASE("LinearNiaDomain: positive coeff Geq 2x-5>=0 -> x>=3") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(2), mpz_class(-5), Relation::Geq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasLower);
    CHECK(d->lower.value == 3);
}

TEST_CASE("LinearNiaDomain: negative coeff Leq -3x+5<=0 -> x>=2") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(-3), mpz_class(5), Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasLower);
    CHECK(d->lower.value == 2);
}

TEST_CASE("LinearNiaDomain: negative coeff Geq -3x+5>=0 -> x<=1") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(-3), mpz_class(5), Relation::Geq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasUpper);
    CHECK(d->upper.value == 1);
}

TEST_CASE("LinearNiaDomain: negative coeff Eq -2x+4=0 -> x=2") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(-2), mpz_class(4), Relation::Eq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    REQUIRE(d->finiteValues.has_value());
    CHECK(d->finiteValues->size() == 1);
    CHECK(*d->finiteValues->begin() == 2);
}

TEST_CASE("LinearNiaDomain: negative coeff Neq -2x+4!=0 -> x!=2") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(-2), mpz_class(4), Relation::Neq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->excludedValues.count(mpz_class(2)));
}

TEST_CASE("LinearNiaDomain: bound conflict 2x+5<=0 and 2x-1>=0") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c1 = makeLinearConstraint(*kernel, "x", mpz_class(2), mpz_class(5), Relation::Leq, mkReason(1));
    auto c2 = makeLinearConstraint(*kernel, "x", mpz_class(2), mpz_class(-1), Relation::Geq, mkReason(2));
    auto r1 = reasoner.run({c1}, ds);
    CHECK(r1.kind == NiaReasoningKind::DomainUpdated);
    auto r2 = reasoner.run({c2}, ds);
    CHECK(r2.kind == NiaReasoningKind::DomainUpdated);

    CHECK(ds.isEmpty("x"));
}

TEST_CASE("LinearNiaDomain: large coeff 1000000x+999999<=0 -> x<=-1") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeLinearConstraint(*kernel, "x", mpz_class(1000000), mpz_class(999999), Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasUpper);
    CHECK(d->upper.value == -1);
}
