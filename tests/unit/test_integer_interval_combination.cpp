#include <doctest/doctest.h>
#include "algebra/linear/IntegerIntervalCombination.h"
#include "search/linear/IntegerReasoner.h"
#include <random>

using namespace xolver;

TEST_CASE("integer interval combination: continued fractions certify thin integer strips") {
    for (const auto& scaleText : {"10000", "100000000", "100000000000000000000"}) {
        const mpz_class scale(scaleText);
        for (long p : {273L, 283L, 991L}) {
            for (long q : {245L, 437L}) {
                BoundedIntegerForm a{{p * scale, -q * scale - 1}, 0, scale - 1};
                BoundedIntegerForm b{{p * scale + 1, -q * scale}, 1, scale};
                WorkBudget budget(4096);
                const auto result = findIntegerIntervalConflict(a, b, budget);
                REQUIRE(result.has_value());
                CHECK(verifyIntegerIntervalConflict(a, b, *result));
                auto corrupted = *result;
                ++corrupted.divisor;
                CHECK_FALSE(verifyIntegerIntervalConflict(a, b, corrupted));
            }
        }
    }
}

TEST_CASE("integer interval combination: signed feasible witnesses never produce a conflict") {
    std::mt19937 random(20261026);
    for (int repeat = 0; repeat < 200; ++repeat) {
        const int dimensions = 1 + random() % 4;
        BoundedIntegerForm a, b;
        mpz_class valueA = 0, valueB = 0;
        for (int i = 0; i < dimensions; ++i) {
            const long x = static_cast<long>(random() % 9) - 4;
            const long ca = static_cast<long>(random() % 41) - 20;
            const long cb = static_cast<long>(random() % 41) - 20;
            a.coefficients.emplace_back(ca); b.coefficients.emplace_back(cb);
            valueA += ca * x; valueB += cb * x;
        }
        a.lower = valueA - static_cast<long>(random() % 5);
        a.upper = valueA + static_cast<long>(random() % 5);
        b.lower = valueB - static_cast<long>(random() % 5);
        b.upper = valueB + static_cast<long>(random() % 5);
        WorkBudget budget(4096);
        CHECK_FALSE(findIntegerIntervalConflict(a, b, budget).has_value());
    }
}

TEST_CASE("IntegerReasoner soundness: bounded-form conflict preserves all bound reasons") {
    IntegerReasoner reasoner;
    const mpq_class scale(100000000);
    LinearFormKey a{{{"x", 283 * scale}, {"y", -245 * scale - 1}}};
    LinearFormKey b{{{"x", 283 * scale + 1}, {"y", -245 * scale}}};
    auto atom = [](LinearFormKey form, Relation relation, mpq_class rhs, SatVar var) {
        return ActiveLinearAtom{NullExpr, -1, relation, true, std::move(form),
                                std::move(rhs), SatLit::positive(var)};
    };
    std::vector<ActiveLinearAtom> atoms{
        atom(a, Relation::Geq, 0, 1), atom(a, Relation::Leq, scale - 1, 2),
        atom(b, Relation::Geq, 1, 3), atom(b, Relation::Leq, scale, 4)};
    auto conflict = reasoner.checkIntervalCombinationConflict(atoms);
    REQUIRE(conflict.has_value());
    REQUIRE(conflict->clause.size() == 4);
    for (std::size_t i = 0; i < 4; ++i) {
        CHECK(conflict->clause[i].var == i + 1);
        CHECK(conflict->clause[i].sign == SatLit::positive(1).sign);
    }
    for (std::size_t removed = 0; removed < atoms.size(); ++removed) {
        auto subset = atoms;
        subset.erase(subset.begin() + static_cast<std::ptrdiff_t>(removed));
        CHECK_FALSE(reasoner.checkIntervalCombinationConflict(subset).has_value());
    }
}
