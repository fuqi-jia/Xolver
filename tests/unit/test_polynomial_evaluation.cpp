#include "algebra/poly/PolynomialEvaluation.h"
#include "algebra/poly/PolynomialKernel.h"
#include <doctest/doctest.h>

using namespace xolver;

TEST_CASE("PolynomialEvaluation: one exact model evaluates shared multivariate polynomials") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const auto polynomial = kernel->add(y, kernel->mul(z, kernel->mul(x, y)));
    const std::unordered_map<std::string, mpz_class> model{{"x", 2}, {"y", 3}, {"z", -4}};
    const auto evaluation = makePolynomialEvaluation(*kernel, model);
    const auto value = evaluation->evaluateInteger(polynomial);
    REQUIRE(value.has_value());
    CHECK(*value == -21);
    CHECK(evaluation->sign(polynomial).value_or(2) == -1);
    const auto zero = evaluation->evaluateInteger(kernel->sub(polynomial, polynomial));
    REQUIRE(zero.has_value());
    CHECK(*zero == 0);
    CHECK(evaluation->sign(kernel->mkOne()).value_or(2) == 1);
}

TEST_CASE("PolynomialEvaluation: large signed integer powers preserve every bit") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const mpz_class large = (mpz_class(1) << 130) + 19;
    const std::unordered_map<std::string, mpz_class> model{{"x", large}, {"y", -large}};
    const auto evaluation = makePolynomialEvaluation(*kernel, model);
    const auto square = evaluation->evaluateInteger(kernel->pow(kernel->sub(x, y), 2));
    REQUIRE(square.has_value());
    CHECK(*square == 4 * large * large);
}

TEST_CASE("PolynomialEvaluation: rational assignments use the same exact snapshot abstraction") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto polynomial = kernel->add(x, kernel->mul(kernel->mkConst(2), y));
    const std::unordered_map<std::string, mpq_class> model{{"x", mpq_class(1, 2)}, {"y", mpq_class(-1, 3)}};
    const auto evaluation = makePolynomialEvaluation(*kernel, model);
    const auto value = evaluation->evaluate(polynomial);
    REQUIRE(value.has_value());
    CHECK(*value == mpq_class(-1, 6));
    CHECK_FALSE(evaluation->evaluateInteger(polynomial).has_value());
    CHECK(evaluation->sign(polynomial).value_or(2) == -1);
}

TEST_CASE("PolynomialEvaluation: missing bindings and later variables never default to zero") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const std::unordered_map<std::string, mpz_class> model{{"x", 3}, {"unused", 7}};
    const auto evaluation = makePolynomialEvaluation(*kernel, model);
    CHECK_FALSE(kernel->findVar("unused").has_value());
    CHECK_FALSE(evaluation->evaluateInteger(y).has_value());
    CHECK_FALSE(evaluation->evaluate(kernel->add(x, y)).has_value());
    const auto late = kernel->mkVar(kernel->getOrCreateVar("late"));
    CHECK_FALSE(evaluation->evaluateInteger(late).has_value());
    const auto constant = evaluation->evaluateInteger(kernel->mkConst(9));
    REQUIRE(constant.has_value());
    CHECK(*constant == 9);
}

TEST_CASE("PolynomialEvaluation: candidate snapshots remain independent after caller mutation") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto polynomial = kernel->mul(x, y);
    std::unordered_map<std::string, mpz_class> model{{"x", 5}, {"y", 7}};
    const auto first = makePolynomialEvaluation(*kernel, model);
    model["x"] = 6;
    model["y"] = -2;
    const auto second = makePolynomialEvaluation(*kernel, model);
    model.clear();
    const auto a = first->evaluateInteger(polynomial), b = second->evaluateInteger(polynomial);
    REQUIRE(a.has_value());
    REQUIRE(b.has_value());
    CHECK(*a == 35);
    CHECK(*b == -12);
    CHECK(first->sign(polynomial).value_or(2) == 1);
    CHECK(second->sign(polynomial).value_or(2) == -1);
}

TEST_CASE("PolynomialEvaluation: a large complete model checks many sparse atoms") {
    auto kernel = createPolynomialKernel();
    std::unordered_map<std::string, mpz_class> model;
    std::vector<PolyId> polynomials;
    for (int i = 0; i < 5000; ++i) {
        const auto name = "model_" + std::to_string(i);
        polynomials.push_back(kernel->mkVar(kernel->getOrCreateVar(name)));
        model.emplace(name, i & 1);
    }
    const auto evaluation = makePolynomialEvaluation(*kernel, model);
    for (size_t i = 0; i < polynomials.size(); ++i) {
        const auto value = evaluation->evaluateInteger(polynomials[i]);
        REQUIRE(value.has_value());
        CHECK(*value == static_cast<unsigned long>(i & 1));
    }
}
