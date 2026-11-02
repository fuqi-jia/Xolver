#include "search/candidate/BoundedSupportProduct.h"
#include "base/WorkBudget.h"
#include <doctest/doctest.h>
#include <string>
#include <vector>

using namespace xolver;

TEST_CASE("Bounded support product matches exhaustive filtered Cartesian order") {
    const std::vector<std::vector<std::vector<int>>> products{
        {}, {{}}, {{0}}, {{1}}, {{-1, 0, 1}, {0, 2}, {3, 0, -2}},
        {{0, 0, 1}, {1, 0}, {0, -1}}, {{1, 2}, {0, 3}, {4}},
        {{0, 1}, {}, {0}}, {{-1, 0, 1}, {-1, 0, 1}, {-1, 0, 1}, {-1, 0, 1}}
    };
    for (const auto& domains : products) {
        for (size_t support = 0; support <= domains.size() + 1; ++support) {
            size_t total = 1;
            for (const auto& domain : domains) total *= domain.size();
            std::vector<std::vector<size_t>> expected;
            for (size_t ordinal = 0; ordinal < total; ++ordinal) {
                size_t remaining = ordinal, nonzero = 0;
                std::vector<size_t> indices;
                for (const auto& domain : domains) {
                    const auto index = remaining % domain.size();
                    remaining /= domain.size();
                    indices.push_back(index);
                    nonzero += domain[index] != 0;
                }
                if (nonzero <= support) expected.push_back(std::move(indices));
            }
            std::vector<std::vector<size_t>> actual;
            CHECK(enumerateBoundedSupportProduct(domains, support,
                [](int value) { return value == 0; },
                [&](const auto& indices) { actual.push_back(indices); return true; }, [] {}));
            CHECK(actual == expected);
        }
    }
}

TEST_CASE("Bounded support product visits sparse high-dimensional domains within structural work") {
    const std::vector<std::vector<int>> domains(58, {-1, 0, 1});
    size_t visits = 0;
    WorkBudget work(1000000);
    CHECK(enumerateBoundedSupportProduct(domains, 2,
        [](int value) { return value == 0; },
        [&](const auto& indices) {
            size_t support = 0;
            for (size_t i = 0; i < indices.size(); ++i) support += domains[i][indices[i]] != 0;
            CHECK(support <= 2);
            ++visits;
            return true;
        }, [&] { work.tick(); }));
    CHECK(visits == 1 + 58*2 + (58*57/2)*4);
}

TEST_CASE("Bounded support product handles mandatory entries and nonnumeric defaults") {
    const std::vector<std::vector<int>> impossible(10000, {1, 2});
    size_t visits = 0;
    CHECK(enumerateBoundedSupportProduct(impossible, 2,
        [](int value) { return value == 0; },
        [&](const auto&) { ++visits; return true; }, [] {}));
    CHECK(visits == 0);
    const std::vector<std::vector<std::string>> words{{"", "a"}, {"b", ""}};
    CHECK(enumerateBoundedSupportProduct(words, 0,
        [](const auto& value) { return value.empty(); },
        [&](const auto& indices) { CHECK((indices == std::vector<size_t>{0, 1})); ++visits; return true; }, [] {}));
    CHECK(visits == 1);
}

TEST_CASE("Bounded support product stops and cancels without retaining enumeration state") {
    const std::vector<std::vector<int>> domains(5, {-1, 0, 1});
    size_t visits = 0;
    CHECK_FALSE(enumerateBoundedSupportProduct(domains, 2,
        [](int value) { return value == 0; },
        [&](const auto&) { return ++visits < 5; }, [] {}));
    CHECK(visits == 5);
    WorkBudget work(10);
    CHECK_THROWS_AS(enumerateBoundedSupportProduct(domains, 2,
        [](int value) { return value == 0; }, [](const auto&) { return true; },
        [&] { work.tick(); }), ResourceExhausted);
    visits = 0;
    CHECK(enumerateBoundedSupportProduct(domains, 2,
        [](int value) { return value == 0; },
        [&](const auto&) { ++visits; return true; }, [] {}));
    CHECK(visits == 1 + 5*2 + (5*4/2)*4);
}
