#include <doctest/doctest.h>
#include "search/nia/core/LinearNiaDomainReasoner.h"
#include "search/nia/core/DomainStore.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/SatSolver.h"
#include <gmpxx.h>
#include <algorithm>

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

TEST_CASE("LinearNiaDomain: affine chains retain endpoint explanations") {
    auto kernel = createPolynomialKernel();
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore domains;
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    // Reverse dependency order requires revisiting x=2y after y=z+1.
    std::vector<NormalizedNiaConstraint> constraints{
        {kernel->sub(x, kernel->mul(kernel->mkConst(2), y)), Relation::Eq, mkReason(3)},
        {kernel->sub(kernel->sub(y, z), kernel->mkConst(1)), Relation::Eq, mkReason(4)},
        makeLinearConstraint(*kernel, "z", 1, 2, Relation::Geq, mkReason(1)),
        makeLinearConstraint(*kernel, "z", 1, -5, Relation::Leq, mkReason(2))};
    reasoner.run(constraints, domains);
    const auto* derived = domains.getDomain("x");
    REQUIRE(derived != nullptr);
    REQUIRE(derived->hasLower);
    REQUIRE(derived->hasUpper);
    CHECK(derived->lower.value == -2);
    CHECK(derived->upper.value == 12);
    for (const auto& bound : {derived->lower, derived->upper}) {
        CHECK(std::find(bound.reasons.begin(), bound.reasons.end(), mkReason(3)) != bound.reasons.end());
        CHECK(std::find(bound.reasons.begin(), bound.reasons.end(), mkReason(4)) != bound.reasons.end());
    }
    CHECK(std::find(derived->lower.reasons.begin(), derived->lower.reasons.end(), mkReason(1)) != derived->lower.reasons.end());
    CHECK(std::find(derived->upper.reasons.begin(), derived->upper.reasons.end(), mkReason(2)) != derived->upper.reasons.end());
}
