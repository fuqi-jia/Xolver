#include <doctest/doctest.h>
#include "search/nra/backend/RootBracket.h"

using namespace xolver;
using nra_backend::compactRootBracket;

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
