#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace zolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// poly = product-of-vars  (+ optional constant), built from a var-name list
static PolyId mkMonomial(PolynomialKernel& k, std::initializer_list<const char*> vars) {
    PolyId p = k.mkOne();
    for (const char* v : vars) p = k.mul(p, k.mkVar(k.getOrCreateVar(v)));
    return p;
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with a>=0,b>=0 -> a>=1, b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    REQUIRE(ds.getDomain("a") != nullptr);
    REQUIRE(ds.getDomain("b") != nullptr);
    CHECK(ds.getDomain("a")->hasLower);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->hasLower);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with a>=0, b in [0,0] -> Conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addUpperBound("b", mpz_class(0), mkReason(4));  // b pinned to 0

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with b sign UNKNOWN -> NoChange (unsound to fire)") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    // b has no lower bound -> could be negative -> a*b>=1 does NOT imply b>=1

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ProductPositivity: a*b >= 0 (no positive const) -> NoChange") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    PolyId poly = mkMonomial(*kernel, {"a", "b"});  // a*b >= 0, L=0, cannot force >=1
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ProductPositivity: a*b*c - 1 = 0 with all>=0 -> a,b,c >= 1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b", "c"}), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
    CHECK(ds.getDomain("c")->lower.value == 1);
}

TEST_CASE("ProductPositivity: multi-monomial a*b + c - 1 >= 0 -> NoChange (milestone 1)") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));

    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId poly = kernel->sub(kernel->add(ab, kernel->mkVar(kernel->getOrCreateVar("c"))),
                              kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}
