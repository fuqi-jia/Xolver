#include <doctest/doctest.h>
#include "algebra/linear/AffineIntegerDomain.h"
#include <array>

using namespace xolver;

namespace {
bool satisfied(const mpq_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}
}

TEST_CASE("AffineIntegerDomain: rational constraints match independent integer enumeration") {
    const std::array relations{Relation::Eq, Relation::Neq, Relation::Lt,
        Relation::Leq, Relation::Gt, Relation::Geq};
    for (int a = -3; a <= 3; ++a) for (int b = -4; b <= 4; ++b)
        for (int ad = 1; ad <= 3; ++ad) for (int bd = 1; bd <= 3; ++bd)
            for (auto relation : relations) for (int minimum : {-4, 0, 3}) {
                mpq_class coefficient(a, ad), constant(b, bd);
                coefficient.canonicalize(); constant.canonicalize();
                AffineIntegerDomain domain;
                domain.constrain(coefficient, constant, relation);
                domain.constrain(1, -5, Relation::Leq);
                std::optional<mpz_class> expected;
                for (int value = minimum; value <= 5; ++value) {
                    if (satisfied(coefficient * value + constant, relation)) {
                        expected = value; break;
                    }
                }
                CHECK(domain.leastAtLeast(minimum) == expected);
            }
}

TEST_CASE("AffineIntegerDomain: disequalities and exact points compose") {
    AffineIntegerDomain domain;
    domain.constrain(1, 2, Relation::Geq);
    domain.constrain(1, 2, Relation::Neq);
    domain.constrain(1, 1, Relation::Neq);
    CHECK(domain.leastAtLeast(-10) == mpz_class(0));
    domain.constrain(2, -1, Relation::Neq); // No integer is excluded.
    CHECK(domain.leastAtLeast(-10) == mpz_class(0));
    domain.constrain(1, 0, Relation::Eq);
    CHECK(domain.leastAtLeast(-10) == mpz_class(0));
    domain.constrain(1, 0, Relation::Neq);
    CHECK_FALSE(domain.leastAtLeast(-10).has_value());
}

TEST_CASE("AffineIntegerDomain: strict bounds remain exact beyond machine integers") {
    const mpz_class large("10000000000000000000000000000000000000000");
    AffineIntegerDomain domain;
    domain.constrain(-2, mpq_class(2 * large + 1), Relation::Lt);
    domain.constrain(1, mpq_class(-large - 1), Relation::Leq);
    REQUIRE(domain.leastAtLeast(1).has_value());
    CHECK(*domain.leastAtLeast(1) == large + 1);
    domain.constrain(1, mpq_class(-large - 1), Relation::Lt);
    CHECK_FALSE(domain.leastAtLeast(1).has_value());
}
