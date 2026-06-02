#include <doctest/doctest.h>
#include "theory/arith/nra/search/HybridPartitionStats.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>

using namespace xolver;

// =============================================================================
// Task NRA-HYB Step 1: partition correctness
// =============================================================================
// These tests pin the partition classifier's behaviour against a small set of
// hand-built polynomials so that the partition data NraSolver dumps under
// XOLVER_NRA_HYB_PARTITION_STATS is mechanically trustworthy. Each test
// constructs PolyIds via the kernel and asserts the partition counts.

TEST_CASE("HybridPartitionStats: empty input gives zero counts") {
    auto kernel = createPolynomialKernel();
    auto r = computePartition({}, *kernel);
    CHECK(r.totalConstraints == 0u);
    CHECK(r.linearConstraints == 0u);
    CHECK(r.nonlinearConstraints == 0u);
    CHECK(r.totalVars == 0u);
    CHECK(r.linearConstraintFraction() == 0.0);
}

TEST_CASE("HybridPartitionStats: x + 1 is linear (degree 1)") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x  = kernel->mkVar(vx);
    PolyId p  = kernel->add(x, kernel->mkConst(mpq_class(1)));
    auto r = computePartition({p}, *kernel);
    CHECK(r.totalConstraints == 1u);
    CHECK(r.linearConstraints == 1u);
    CHECK(r.nonlinearConstraints == 0u);
    CHECK(r.totalVars == 1u);
    CHECK(r.pureLinearVars == 1u);
    CHECK(r.pureNonlinearVars == 0u);
    CHECK(r.mixedVars == 0u);
}

TEST_CASE("HybridPartitionStats: x^2 is nonlinear (degree 2)") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x  = kernel->mkVar(vx);
    PolyId x2 = kernel->mul(x, x);
    auto r = computePartition({x2}, *kernel);
    CHECK(r.totalConstraints == 1u);
    CHECK(r.linearConstraints == 0u);
    CHECK(r.nonlinearConstraints == 1u);
    CHECK(r.pureNonlinearVars == 1u);
    CHECK(r.pureLinearVars == 0u);
    CHECK(r.mixedVars == 0u);
}

TEST_CASE("HybridPartitionStats: x*y is nonlinear (bilinear, total deg 2)") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(vx);
    PolyId y = kernel->mkVar(vy);
    PolyId xy = kernel->mul(x, y);
    auto r = computePartition({xy}, *kernel);
    CHECK(r.totalConstraints == 1u);
    CHECK(r.linearConstraints == 0u);
    CHECK(r.nonlinearConstraints == 1u);
    CHECK(r.totalVars == 2u);
    CHECK(r.pureNonlinearVars == 2u);
    CHECK(r.mixedVars == 0u);
}

TEST_CASE("HybridPartitionStats: mixed L+N gives V_M for shared var") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(vx);
    PolyId y = kernel->mkVar(vy);
    // L: x + y - 1  (linear, vars {x,y})
    // N: x*x - 4   (nonlinear, vars {x})
    PolyId pL = kernel->sub(kernel->add(x, y), kernel->mkConst(mpq_class(1)));
    PolyId pN = kernel->sub(kernel->mul(x, x), kernel->mkConst(mpq_class(4)));
    auto r = computePartition({pL, pN}, *kernel);
    CHECK(r.totalConstraints == 2u);
    CHECK(r.linearConstraints == 1u);
    CHECK(r.nonlinearConstraints == 1u);
    CHECK(r.totalVars == 2u);
    // x is in BOTH L and N -> V_M (mixed).
    CHECK(r.mixedVars == 1u);
    // y is only in L -> V_L (pure linear).
    CHECK(r.pureLinearVars == 1u);
    CHECK(r.pureNonlinearVars == 0u);
    CHECK(r.linearConstraintFraction() == doctest::Approx(0.5));
    CHECK(r.mixedVarFraction() == doctest::Approx(0.5));
}

TEST_CASE("HybridPartitionStats: constant polynomial counts as linear (degree 0)") {
    auto kernel = createPolynomialKernel();
    PolyId pConst = kernel->mkConst(mpq_class(7));
    auto r = computePartition({pConst}, *kernel);
    CHECK(r.totalConstraints == 1u);
    // Constants have no monomials of degree > 1, so the classifier treats
    // them as linear (degree 0 <= 1). No variables.
    CHECK(r.linearConstraints == 1u);
    CHECK(r.totalVars == 0u);
}

TEST_CASE("HybridPartitionStats: NullPoly slots are skipped") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    auto r = computePartition({NullPoly, x, NullPoly}, *kernel);
    // totalConstraints is the input vector size; the null slots are
    // counted in total but not classified into L or N.
    CHECK(r.totalConstraints == 3u);
    CHECK(r.linearConstraints == 1u);
    CHECK(r.nonlinearConstraints == 0u);
}
