#include <doctest/doctest.h>
#include "search/refute/MonomialSquares.h"

using namespace xolver;
namespace {
RationalPolynomial monomial(const MonomialKey& key) {
    RationalPolynomial result;
    result.addTerm(key, 1);
    result.normalize();
    return result;
}
void checkIdentity(const RationalPolynomial& input, const MonomialSquareDecomposition& result) {
    auto reconstructed = result.remainder;
    for (const auto& square : result.squares) {
        CHECK(square.coefficient > 0);
        auto term = monomial(square.weight) * (monomial(square.left) - monomial(square.right)).pow(2);
        term *= square.coefficient;
        reconstructed += term;
    }
    reconstructed -= input;
    reconstructed.normalize();
    CHECK(reconstructed.isZero());
}
}

TEST_CASE("Monomial squares: mixed degrees share negative centers exactly") {
    const auto x = RationalPolynomial::fromVar(17, 1, 1);
    const auto y = RationalPolynomial::fromVar(902, 1, 1);
    auto cross = x * y;
    cross *= 5;
    const auto input = x * x * y + x * y * y + x * x + y * y + x + y - cross;
    WorkBudget budget(10000);
    const auto result = decomposeMonomialSquares(input, [](const auto&) { return true; }, budget);
    REQUIRE(result.squares.size() >= 3);
    checkIdentity(input, result);
    for (const auto& [key, coefficient] : result.remainder.terms()) {
        (void)key;
        CHECK(coefficient >= 0);
    }
}

TEST_CASE("Monomial squares: unknown weights remain in the remainder") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto y = RationalPolynomial::fromVar(1, 1, 1);
    const auto input = x * (y - RationalPolynomial::fromConstant(1)).pow(2);
    WorkBudget budget(1000);
    const auto result = decomposeMonomialSquares(input, [](const auto& key) { return key.empty(); }, budget);
    CHECK(result.squares.empty());
    checkIdentity(input, result);
    CHECK(input.evaluateRational({{0, -1}, {1, 0}}) < 0);
}

TEST_CASE("Monomial squares: partial identities do not certify a negative residual") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto input = (x - RationalPolynomial::fromConstant(1)).pow(2) - RationalPolynomial::fromConstant(2);
    WorkBudget budget(1000);
    const auto result = decomposeMonomialSquares(input, [](const auto&) { return true; }, budget);
    checkIdentity(input, result);
    CHECK(result.remainder.evaluateRational({{0, 1}}) < 0);
}

TEST_CASE("Monomial squares: rational and duplicate coefficients preserve identities") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    auto input = (x - RationalPolynomial::fromConstant(1)).pow(2);
    input *= mpq_class(7, 13);
    auto duplicate = input;
    duplicate.appendTerms(input);
    WorkBudget budget(1000);
    const auto result = decomposeMonomialSquares(duplicate, [](const auto&) { return true; }, budget);
    checkIdentity(duplicate, result);
    CHECK(result.remainder.isZero());
}

TEST_CASE("Monomial squares: exhausted allocations propagate without a sign verdict") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto input = (x - RationalPolynomial::fromConstant(1)).pow(2);
    WorkBudget budget(1);
    CHECK_THROWS_AS(decomposeMonomialSquares(input, [](const auto&) { return true; }, budget), ResourceExhausted);
    WorkBudget retry(1000);
    const auto result = decomposeMonomialSquares(input, [](const auto&) { return true; }, retry);
    REQUIRE_FALSE(result.squares.empty());
    checkIdentity(input, result);
}

TEST_CASE("Monomial equation reduction: exact divisibility includes a zero leading factor") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto y = RationalPolynomial::fromVar(1, 1, 1);
    const auto z = RationalPolynomial::fromVar(2, 1, 1);
    const auto equation = x * z - y;
    const auto input = x * x * z + y;
    WorkBudget budget(1000);
    const auto reduction = reduceByMonomialEquation(input, equation, 2, budget);
    REQUIRE(reduction);
    CHECK((input - reduction->quotient * equation - reduction->remainder).isZero());
    CHECK(reduction->remainder.degree(2) <= 0);
    CHECK(reduction->remainder.evaluateRational({{0, 0}, {1, 3}, {2, 9}}) == 3);
    CHECK_FALSE(reduceByMonomialEquation(z, equation, 2, budget));
    CHECK_FALSE(reduceByMonomialEquation(x * z * z + z, equation, 2, budget));
}
