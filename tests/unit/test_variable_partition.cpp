// HYB-1 VariablePartition unit tests. Pin the partition classification
// behavior independent of any downstream hybrid solver.
#include <doctest/doctest.h>
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

TEST_CASE("HYB-1 VariablePartition: x in [-100, 100] is bounded with 8 bits") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-100), mkReason(1));
    ds.addUpperBound("x", mpz_class(100), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // Atom: x*x = 0 — a nonlinear constraint mentioning x without
    // introducing an additional single-var bound (extractSingleVarBound
    // bails on the x^2 power).
    PolyId xsq = kernel->pow(x, 2);
    NormalizedNiaConstraint c{xsq, Relation::Eq, mkReason(3)};

    auto pr = vp.partition({c}, ds, /*maxBitWidth=*/32);
    REQUIRE(pr.totalVars() == 1);
    CHECK(pr.boundedCount() == 1);
    CHECK(pr.unboundedCount() == 0);
    CHECK(pr.info.at("x").hasLower);
    CHECK(pr.info.at("x").hasUpper);
    CHECK(pr.info.at("x").lower == -100);
    CHECK(pr.info.at("x").upper == 100);
    // 8-bit signed covers [-128, 127] which contains [-100, 100].
    CHECK(pr.info.at("x").bitWidth == 8);
    CHECK(pr.info.at("x").isBounded);
}

TEST_CASE("HYB-1 VariablePartition: only-upper-bound var is unbounded") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;
    ds.addUpperBound("y", mpz_class(50), mkReason(1));
    // No lower bound.

    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    // Nonlinear constraint to avoid bound-injection from extractSingleVarBound.
    PolyId ysq = kernel->pow(y, 2);
    NormalizedNiaConstraint c{ysq, Relation::Eq, mkReason(2)};

    auto pr = vp.partition({c}, ds, 32);
    REQUIRE(pr.totalVars() == 1);
    CHECK(pr.boundedCount() == 0);
    CHECK(pr.unboundedCount() == 1);
    CHECK(pr.info.at("y").hasUpper);
    CHECK(!pr.info.at("y").hasLower);
    CHECK(!pr.info.at("y").isBounded);
}

TEST_CASE("HYB-1 VariablePartition: explicit bound atoms augment empty DomainStore") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;  // empty

    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));
    // z + (-10) >= 0   =>   z >= 10
    PolyId atomLo = kernel->add(z, kernel->mkConst(mpq_class(-10)));
    // z + (-100) <= 0  =>  z <= 100
    PolyId atomHi = kernel->add(z, kernel->mkConst(mpq_class(-100)));
    NormalizedNiaConstraint c1{atomLo, Relation::Geq, mkReason(1)};
    NormalizedNiaConstraint c2{atomHi, Relation::Leq, mkReason(2)};

    auto pr = vp.partition({c1, c2}, ds, 32);
    REQUIRE(pr.info.count("z"));
    CHECK(pr.info.at("z").hasLower);
    CHECK(pr.info.at("z").lower == 10);
    CHECK(pr.info.at("z").hasUpper);
    CHECK(pr.info.at("z").upper == 100);
    CHECK(pr.info.at("z").isBounded);
}

TEST_CASE("HYB-1 VariablePartition: oversized bound becomes unbounded under cap") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;
    // [0, 2^33 - 1] needs 34 bits signed; under maxBitWidth=32 it falls
    // to unbounded.
    ds.addLowerBound("w", mpz_class(0), mkReason(1));
    mpz_class bigUpper;
    mpz_ui_pow_ui(bigUpper.get_mpz_t(), 2, 33);
    bigUpper -= 1;
    ds.addUpperBound("w", bigUpper, mkReason(2));

    PolyId w = kernel->mkVar(kernel->getOrCreateVar("w"));
    NormalizedNiaConstraint c{w, Relation::Geq, mkReason(3)};

    auto pr = vp.partition({c}, ds, 32);
    REQUIRE(pr.info.count("w"));
    CHECK(pr.info.at("w").hasLower);
    CHECK(pr.info.at("w").hasUpper);
    CHECK(pr.info.at("w").bitWidth > 32);
    CHECK(!pr.info.at("w").isBounded);
    CHECK(pr.unboundedCount() == 1);
}

TEST_CASE("HYB-1 VariablePartition: equality atom forces tight pin") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;

    PolyId v = kernel->mkVar(kernel->getOrCreateVar("v"));
    // v + (-7) = 0  =>  v = 7
    PolyId atomEq = kernel->add(v, kernel->mkConst(mpq_class(-7)));
    NormalizedNiaConstraint c{atomEq, Relation::Eq, mkReason(1)};

    auto pr = vp.partition({c}, ds, 32);
    REQUIRE(pr.info.count("v"));
    CHECK(pr.info.at("v").hasLower);
    CHECK(pr.info.at("v").hasUpper);
    CHECK(pr.info.at("v").lower == 7);
    CHECK(pr.info.at("v").upper == 7);
    CHECK(pr.info.at("v").isBounded);
}

TEST_CASE("HYB-1 VariablePartition: averages aggregate correctly") {
    auto kernel = createPolynomialKernel();
    VariablePartition vp(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addUpperBound("a", mpz_class(15), mkReason(2));  // 5 bits
    ds.addLowerBound("b", mpz_class(0), mkReason(3));
    ds.addUpperBound("b", mpz_class(255), mkReason(4));  // 9 bits
    PolyId a = kernel->mkVar(kernel->getOrCreateVar("a"));
    PolyId b = kernel->mkVar(kernel->getOrCreateVar("b"));
    NormalizedNiaConstraint c1{a, Relation::Geq, mkReason(5)};
    NormalizedNiaConstraint c2{b, Relation::Geq, mkReason(6)};

    auto pr = vp.partition({c1, c2}, ds, 32);
    CHECK(pr.boundedCount() == 2);
    CHECK(pr.unboundedCount() == 0);
    CHECK(pr.maxBitWidthBounded() == 9);
    CHECK(pr.averageBitWidthBounded() == 7.0);
}
