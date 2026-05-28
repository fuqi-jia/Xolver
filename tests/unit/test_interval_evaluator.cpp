#include <doctest/doctest.h>
#include "theory/arith/interval/IntervalEvaluator.h"
#include "theory/arith/interval/ReasonedBoxZ.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// Build interval constraint: a*x^n + ... + c rel 0
static IntervalConstraint makeIntervalConstraint(
    PolynomialKernel& kernel, const std::string& var,
    const std::vector<mpz_class>& coeffs, Relation rel, SatLit reason) {

    PolyId varPoly = kernel.mkVar(kernel.getOrCreateVar(var));
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

static ReasonedBoxZ makeBox(const std::string& var, mpz_class lo, mpz_class hi,
                           const std::vector<SatLit>& reasons) {
    ReasonedBoxZ box;
    box.set(var, ReasonedInterval{IntervalZ{lo, hi}, reasons});
    return box;
}

TEST_CASE("IntervalEvaluator: x^2 - 1 <= 0 on [-2,2] -> not violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(-2), mpz_class(2), {mkReason(1), mkReason(2)});

    // x^2 - 1 <= 0
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(-1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: x^3 + 1 <= 0 on [0,2] -> violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(0), mpz_class(2), {mkReason(1), mkReason(2)});

    // x^3 + 1 <= 0
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::DefinitelyViolated);
    CHECK(!r.usedReasons.empty());
}

TEST_CASE("IntervalEvaluator: x^3 - 8 <= 0 on [0,2] -> not violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(0), mpz_class(2), {mkReason(1), mkReason(2)});

    // x^3 - 8 <= 0
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(-8)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: no upper bound -> skip") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    ReasonedBoxZ box;
    // Variable "x" not in box at all -> no bounds

    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: multivariate -> skip") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(-2), mpz_class(2), {mkReason(1), mkReason(2)});

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId poly = kernel->add(kernel->pow(x, 2), kernel->pow(y, 2));

    auto c = IntervalConstraint{poly, Relation::Leq, mkReason(5)};
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: x^2 - 4 = 0 on [3,5] -> violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(3), mpz_class(5), {mkReason(1), mkReason(2)});

    // x^2 - 4 = 0
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(-4)},
                                     Relation::Eq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::DefinitelyViolated);
}

TEST_CASE("IntervalEvaluator: 2x^2 + 3x + 1 <= 0 on [-3,-2] -> interval too wide, NoChange") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(-3), mpz_class(-2), {mkReason(1), mkReason(2)});

    // 2x^2 + 3x + 1 <= 0
    // On [-3,-2]: true values are [3, 10], all > 0.
    // But interval arithmetic gives [0, 13] (over-approx), lo=0 not > 0.
    // This is expected: interval arithmetic is conservative.
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(2), mpz_class(3), mpz_class(1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: x^3 + 1 <= 0 on [0,100000] -> violated") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator eval(*kernel);
    auto box = makeBox("x", mpz_class(0), mpz_class(100000), {mkReason(1), mkReason(2)});

    // x^3 + 1 <= 0
    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::DefinitelyViolated);
}
