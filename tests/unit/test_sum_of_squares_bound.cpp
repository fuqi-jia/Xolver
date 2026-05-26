#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/SumOfSquaresBoundReasoner.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace zolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// Build a normalized constraint: x^2 + y^2 + c rel 0
static NormalizedNiaConstraint makeSOSConstraint(
    PolynomialKernel& kernel, const std::string& x, const std::string& y,
    const mpz_class& c, Relation rel, SatLit reason) {

    PolyId xVar = kernel.mkVar(kernel.getOrCreateVar(x));
    PolyId yVar = kernel.mkVar(kernel.getOrCreateVar(y));
    PolyId x2 = kernel.pow(xVar, 2);
    PolyId y2 = kernel.pow(yVar, 2);
    PolyId cPoly = kernel.mkConst(mpq_class(c));
    PolyId poly = kernel.add(kernel.add(x2, y2), cPoly);
    return {poly, rel, reason};
}

TEST_CASE("SumOfSquaresBound: x^2+y^2-65=0 -> bounds [-8,8]") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    // x^2 + y^2 - 65 = 0  =>  c = -65
    auto c = makeSOSConstraint(*kernel, "x", "y", mpz_class(-65), Relation::Eq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* dx = ds.getDomain("x");
    REQUIRE(dx != nullptr);
    CHECK(dx->hasLower);
    CHECK(dx->hasUpper);
    CHECK(dx->lower.value == -8);
    CHECK(dx->upper.value == 8);

    const IntDomain* dy = ds.getDomain("y");
    REQUIRE(dy != nullptr);
    CHECK(dy->lower.value == -8);
    CHECK(dy->upper.value == 8);
}

TEST_CASE("SumOfSquaresBound: x^2+y^2+1<=0 -> UNSAT") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    // x^2 + y^2 + 1 <= 0  =>  sum of squares <= -1: impossible
    auto c = makeSOSConstraint(*kernel, "x", "y", mpz_class(1), Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("SumOfSquaresBound: x^2+y^2-65<=0 -> bounds [-8,8]") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    auto c = makeSOSConstraint(*kernel, "x", "y", mpz_class(-65), Relation::Leq, mkReason(1));
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* dx = ds.getDomain("x");
    REQUIRE(dx != nullptr);
    CHECK(dx->lower.value == -8);
    CHECK(dx->upper.value == 8);
}

TEST_CASE("SumOfSquaresBound: linear constraint ignored") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId poly = kernel->add(kernel->mul(two, x), kernel->mkConst(mpq_class(5)));

    auto c = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(1)};
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SumOfSquaresBound: single variable x^2-4=0 -> bounds [-2,2]") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId x2 = kernel->pow(x, 2);
    PolyId cPoly = kernel->mkConst(mpq_class(mpz_class(-4)));
    PolyId poly = kernel->add(x2, cPoly);

    auto c = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(1)};
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->lower.value == -2);
    CHECK(d->upper.value == 2);
}

TEST_CASE("SumOfSquaresBound: three variables x^2+y^2+z^2-27=0") {
    auto kernel = createPolynomialKernel();
    SumOfSquaresBoundReasoner reasoner(*kernel);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));
    PolyId poly = kernel->add(kernel->add(kernel->pow(x, 2), kernel->pow(y, 2)),
                               kernel->add(kernel->pow(z, 2), kernel->mkConst(mpq_class(mpz_class(-27)))));

    auto c = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(1)};
    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);

    const IntDomain* dx = ds.getDomain("x");
    REQUIRE(dx != nullptr);
    CHECK(dx->lower.value == -5); // floor(sqrt(27)) = 5
    CHECK(dx->upper.value == 5);
}
