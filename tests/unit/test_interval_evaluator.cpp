#include <doctest/doctest.h>
#include "algebra/interval/IntervalEvaluator.h"
#include "algebra/interval/ReasonedBox.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/SatSolver.h"
#include <gmpxx.h>
#include <algorithm>

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

static ReasonedBox makeBox(const std::string& var, mpz_class lo, mpz_class hi,
                           const std::vector<SatLit>& reasons) {
    ReasonedBox box;
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
    ReasonedBox box;
    // Variable "x" not in box at all -> no bounds

    auto c = makeIntervalConstraint(*kernel, "x", {mpz_class(1), mpz_class(0), mpz_class(0), mpz_class(1)},
                                     Relation::Leq, mkReason(3));
    auto r = eval.run(c, box);
    CHECK(r.status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: missing multivariate coordinate stays open") {
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

TEST_CASE("IntervalEvaluator: multivariate powers carry every bound premise") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator evaluator(*kernel);
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto polynomial = kernel->add(kernel->mul(kernel->pow(x, 2), kernel->pow(y, 2)),
                                        kernel->mkConst(mpq_class(1)));
    ReasonedBox box;
    box.set("x", {{-3, 2}, {mkReason(1), mkReason(2)}});
    box.set("y", {{-2, 3}, {mkReason(3), mkReason(4)}});
    const auto result = evaluator.run({polynomial, Relation::Leq, mkReason(5)}, box);
    REQUIRE(result.status == IntervalEvalStatus::DefinitelyViolated);
    REQUIRE(result.usedReasons.size() == 4);
    for (SatVar i = 1; i <= 4; ++i)
        CHECK(std::find(result.usedReasons.begin(), result.usedReasons.end(), mkReason(i)) != result.usedReasons.end());
    // Independent point evaluations include negative coordinates and zero;
    // no dependency assumption may strengthen the polynomial's lower bound.
    for (int a = -3; a <= 2; ++a) for (int b = -2; b <= 3; ++b) {
        const auto value = kernel->evalInteger(polynomial, {{"x", mpz_class(a)}, {"y", mpz_class(b)}});
        REQUIRE(value.has_value());
        CHECK(*value > 0);
    }
    CHECK(evaluator.run({polynomial, Relation::Geq, mkReason(5)}, box).status == IntervalEvalStatus::NoChange);
}

TEST_CASE("IntervalEvaluator: multivariate signed strict bounds survive context replacement") {
    auto kernel = createPolynomialKernel();
    IntervalEvaluator evaluator(*kernel);
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto polynomial = kernel->mul(x, y);
    ReasonedBox box;
    box.set("x", {{-3, -2}, {mkReason(1), mkReason(2)}});
    box.set("y", {{2, 3}, {mkReason(3), mkReason(4)}});
    CHECK(evaluator.run({polynomial, Relation::Gt, mkReason(5)}, box).status == IntervalEvalStatus::DefinitelyViolated);
    box.set("y", {{-3, 0}, {mkReason(6), mkReason(7)}});
    const auto result = evaluator.run({polynomial, Relation::Lt, mkReason(8)}, box);
    REQUIRE(result.status == IntervalEvalStatus::DefinitelyViolated);
    CHECK(std::find(result.usedReasons.begin(), result.usedReasons.end(), mkReason(3)) == result.usedReasons.end());
    CHECK(std::find(result.usedReasons.begin(), result.usedReasons.end(), mkReason(6)) != result.usedReasons.end());
    box.clear();
    CHECK(evaluator.run({polynomial, Relation::Gt, mkReason(5)}, box).status == IntervalEvalStatus::NoChange);
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
