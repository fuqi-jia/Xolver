#include <doctest/doctest.h>
#include "search/nra/backend/RootBracket.h"

using namespace xolver;
using nra_backend::compactRootBracket;

TEST_CASE("root bracket: certified separation has no fixed precision cutoff") {
    using nra_backend::RootBracket;
    using nra_backend::separateRootBrackets;
    mpz_class scale(1); scale <<= 256;
    for (const int sign : {-1, 1}) {
        const mpq_class left = mpq_class(sign) + mpq_class(1, scale);
        const mpq_class right = mpq_class(sign) + mpq_class(3, scale);
        size_t comparisons = 0;
        auto compare = [&](const mpq_class& point, const mpq_class& root) -> std::optional<int> {
            ++comparisons;
            return cmp(point, root);
        };
        WorkBudget work;
        const RootBracket initial{sign - 1, sign + 1};
        const auto result = separateRootBrackets(initial, initial,
            [&](const mpq_class& point) { return compare(point, left); },
            [&](const mpq_class& point) { return compare(point, right); }, work);
        REQUIRE(result);
        CHECK(comparisons > 40);
        CHECK(result->first.upper < result->second.lower);
        CHECK(initial.lower <= result->first.lower);
        CHECK(result->second.upper <= initial.upper);
        CHECK(result->first.lower <= left);
        CHECK(left <= result->first.upper);
        CHECK(result->second.lower <= right);
        CHECK(right <= result->second.upper);
    }
}

TEST_CASE("root bracket: rational boundaries retain the root on either side") {
    using nra_backend::RootBracket;
    using nra_backend::separateRootBrackets;
    // The comparison is exact for sqrt(2), including negative test points.
    auto compareRoot = [](const mpq_class& point) -> std::optional<int> {
        if (point < 0) return -1;
        const mpq_class square = point * point;
        return cmp(square, mpq_class(2));
    };
    for (const bool rootFirst : {false, true}) {
        const mpq_class rational = rootFirst ? mpq_class(3, 2) : mpq_class(1);
        auto compareRational = [&](const mpq_class& point) -> std::optional<int> {
            return cmp(point, rational);
        };
        WorkBudget work;
        const RootBracket root{1, 2}, point{rational, rational};
        const auto result = rootFirst
            ? separateRootBrackets(root, point, compareRoot, compareRational, work)
            : separateRootBrackets(point, root, compareRational, compareRoot, work);
        REQUIRE(result);
        CHECK(result->first.upper < result->second.lower);
        const auto& refined = rootFirst ? result->first : result->second;
        CHECK(refined.lower >= 1);
        CHECK(refined.upper <= 2);
        CHECK(refined.lower * refined.lower <= 2);
        CHECK(refined.upper * refined.upper >= 2);
        const auto& exact = rootFirst ? result->second : result->first;
        CHECK(exact.lower == rational);
        CHECK(exact.upper == rational);
    }
}

TEST_CASE("root bracket: inconclusive comparisons and caller exhaustion cannot certify separation") {
    using nra_backend::RootBracket;
    using nra_backend::separateRootBrackets;
    const RootBracket initial{0, 2};
    auto unknown = [](const mpq_class&) -> std::optional<int> { return std::nullopt; };
    WorkBudget work;
    CHECK_FALSE(separateRootBrackets(initial, initial, unknown, unknown, work));
    CHECK(initial.lower == 0);
    CHECK(initial.upper == 2);
    auto left = [](const mpq_class& point) -> std::optional<int> { return cmp(point, mpq_class(1, 3)); };
    auto right = [](const mpq_class& point) -> std::optional<int> { return cmp(point, mpq_class(2, 3)); };
    WorkBudget exhausted(1);
    CHECK_THROWS_AS(separateRootBrackets(initial, initial, left, right, exhausted), ResourceExhausted);
    WorkBudget disjoint;
    const auto result = separateRootBrackets({0, 0}, {1, 1}, unknown, unknown, disjoint);
    REQUIRE(result);
    CHECK(result->first.upper == 0);
    CHECK(result->second.lower == 1);
}

TEST_CASE("root bracket: redundant dyadic precision preserves the isolated root") {
    mpz_class denominator(1); denominator <<= 16384;
    mpq_class epsilon(1, denominator);
    const mpq_class lower = 1 + epsilon, upper = 2 - epsilon;
    WorkBudget work;
    auto bracket = compactRootBracket({1, 0, -2}, lower, upper, 128, work);
    REQUIRE(bracket.has_value());
    CHECK(bracket->lower >= lower);
    CHECK(bracket->upper <= upper);
    CHECK(bracket->lower < bracket->upper);
    CHECK(bracket->lower * bracket->lower < 2);
    CHECK(bracket->upper * bracket->upper > 2);
    CHECK(mpz_sizeinbase(bracket->lower.get_den_mpz_t(), 2) < 16);
    CHECK(mpz_sizeinbase(bracket->upper.get_den_mpz_t(), 2) < 16);

    WorkBudget negativeWork;
    auto negative = compactRootBracket({1, 0, -2}, -upper, -lower, 128, negativeWork);
    REQUIRE(negative.has_value());
    CHECK(negative->lower * negative->lower > 2);
    CHECK(negative->upper * negative->upper < 2);
}

TEST_CASE("root bracket: verified rational roots are represented as points") {
    mpz_class denominator(1); denominator <<= 16384;
    mpq_class epsilon(1, denominator);
    WorkBudget work;
    auto bracket = compactRootBracket({1, -1}, 1 - epsilon, 1 + epsilon, 128, work);
    REQUIRE(bracket.has_value());
    CHECK(bracket->lower == 1);
    CHECK(bracket->upper == 1);
    auto invalidPoint = compactRootBracket({1, 0, -2}, 1, 1, 128, work);
    CHECK_FALSE(invalidPoint.has_value());
}

TEST_CASE("root bracket: precision and work exhaustion remain inconclusive") {
    // A certified sqrt(2) bracket narrower than 2^-100 cannot fit a 32-bit
    // Horner intermediate budget. It must never become a different root.
    mpz_class scale(1); scale <<= 200;
    mpz_class twiceSquare = 2 * scale * scale, floorRoot;
    mpz_sqrt(floorRoot.get_mpz_t(), twiceSquare.get_mpz_t());
    mpq_class lower(floorRoot, scale), upper(floorRoot + 1, scale);
    lower.canonicalize(); upper.canonicalize();
    WorkBudget work;
    CHECK_FALSE(compactRootBracket({1, 0, -2}, lower, upper, 32, work).has_value());
    WorkBudget exhausted(1);
    CHECK_THROWS_AS(compactRootBracket({1, 0, -2}, 1, 2, 128, exhausted), ResourceExhausted);
    WorkBudget ordinary;
    auto simple = compactRootBracket({1, 0, -2}, 1, 2, 128, ordinary);
    REQUIRE(simple.has_value());
    CHECK(simple->lower == 1);
    CHECK(simple->upper == 2);
}
