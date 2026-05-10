#include <doctest/doctest.h>
#include "theory/arith/nia/IntervalEvaluator.h"
#include "theory/arith/nia/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace nlcolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// Build normalized constraint: a*x^n + ... + c rel 0
static NormalizedNiaConstraint makePolyConstraint(
    PolynomialKernel& kernel, const std::string& var,
    const std::vector<mpz_class>& coeffs, Relation rel, SatLit reason) {

    PolyId varPoly = kernel.mkVar(var);
    PolyId result = kernel.mkZero();
    for (size_t i = 0; i < coeffs.size(); ++i) {
        if (coeffs[i] == 0) continue;
        mpz_class c = coeffs[i];
        size_t power = coeffs.size() - 1 - i;
        PolyId term = kernel.mkConst(mpq_class(c));
        if (power > 0) {
            term = kernel.mul(term, kernel.pow(varPoly, static_cast<uint32_t>(power)));
        }
        result = kernel.add(result, term);
    }
    return {result, rel, reason};
}

TEST_CASE("IntervalEvaluator: x^2 - 1 <= 0 on [-2,2] -> not violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-2), mkReason(1));
    ds.addUpperBound("x", mpz_class(2), mkReason(2));

    // x^2 - 1 <= 0
    auto c = makePolyConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(-1)},
                                 Relation::Leq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("IntervalEvaluator: x^3 + 1 <= 0 on [0,2] -> violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(2), mkReason(2));

    // x^3 + 1 <= 0
    auto c = makePolyConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                 Relation::Leq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("IntervalEvaluator: x^3 - 8 <= 0 on [0,2] -> not violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(2), mkReason(2));

    // x^3 - 8 <= 0
    auto c = makePolyConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(-8)},
                                 Relation::Leq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("IntervalEvaluator: no upper bound -> skip") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    // No upper bound

    auto c = makePolyConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                 Relation::Leq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("IntervalEvaluator: multivariate -> skip") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-2), mkReason(1));
    ds.addUpperBound("x", mpz_class(2), mkReason(2));
    ds.addLowerBound("y", mpz_class(-2), mkReason(3));
    ds.addUpperBound("y", mpz_class(2), mkReason(4));

    PolyId x = kernel->mkVar("x");
    PolyId y = kernel->mkVar("y");
    PolyId poly = kernel->add(kernel->pow(x, 2), kernel->pow(y, 2));

    auto c = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(5)};
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("IntervalEvaluator: x^2 - 4 = 0 on [3,5] -> violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(3), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    // x^2 - 4 = 0
    auto c = makePolyConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(-4)},
                                 Relation::Eq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("IntervalEvaluator: 2x^2 + 3x + 1 <= 0 on [-3,-2] -> interval too wide, NoChange") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-3), mkReason(1));
    ds.addUpperBound("x", mpz_class(-2), mkReason(2));

    // 2x^2 + 3x + 1 <= 0
    // On [-3,-2]: true values are [3, 10], all > 0.
    // But interval arithmetic gives [0, 13] (over-approx), lo=0 not > 0.
    // This is expected: interval arithmetic is conservative.
    auto c = makePolyConstraint(*kernel, "x", {mpz_class(2), mpz_class(3), mpz_class(1)},
                                 Relation::Leq, mkReason(3));
    auto r = eval.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}
