#include <doctest/doctest.h>
#include "search/candidate/BoundaryCandidates.h"
#include <random>
#include <stdexcept>

using namespace xolver;

TEST_CASE("explained candidates: resolve an exhausted domain and skip unrelated choices") {
    constexpr size_t count = 20;
    std::vector<int> prefix;
    size_t pushes = 0, pops = 0;
    CandidateSearchStatistics statistics;
    const auto result = searchBoundaryCandidates(count,
        [](size_t) { return CandidateChoices<int>{{0, 1}, {}}; },
        [&](size_t depth, int value) {
            REQUIRE(prefix.size() == depth);
            prefix.push_back(value);
            ++pushes;
            if (depth == count - 1 && prefix.front() == 0)
                return CandidatePropagation::reject({depth, 0, depth});
            return CandidatePropagation::accept();
        },
        [&](size_t depth) {
            CHECK(prefix.size() == depth + 1);
            prefix.pop_back();
            ++pops;
        },
        [&]() -> std::optional<std::vector<int>> { return prefix; }, &statistics);
    REQUIRE(result.has_value());
    CHECK(result->front() == 1);
    CHECK(result->back() == 0);
    CHECK(pushes == 41);
    CHECK(pops == pushes);
    CHECK(prefix.empty());
    CHECK(statistics.backjumps == 1);
    CHECK(statistics.skippedLevels == 18);
}

TEST_CASE("explained candidates: prefix-dependent domains retain their generating reasons") {
    constexpr size_t count = 12;
    std::vector<int> prefix;
    CandidateSearchStatistics statistics;
    const auto result = searchBoundaryCandidates(count,
        [&](size_t depth) {
            if (depth == count - 1) return CandidateChoices<int>{{prefix[1]}, {1}};
            return CandidateChoices<int>{{0, 1}, {}};
        },
        [&](size_t depth, int value) {
            prefix.push_back(value);
            if (depth == count - 1 && value == 0) return CandidatePropagation::reject({depth});
            return CandidatePropagation::accept();
        },
        [&](size_t) { prefix.pop_back(); },
        [&]() -> std::optional<std::vector<int>> { return prefix; }, &statistics);
    REQUIRE(result.has_value());
    CHECK((*result)[0] == 0);
    CHECK((*result)[1] == 1);
    CHECK(result->back() == 1);
    CHECK(statistics.backjumps == 1);
    CHECK(statistics.skippedLevels == 9);
    CHECK(prefix.empty());
}

TEST_CASE("explained candidates: malformed conflict or domain reasons unwind the active prefix") {
    for (bool malformedDomain : {false, true}) {
        std::vector<int> prefix;
        size_t pushes = 0, pops = 0;
        auto run = [&]() {
            return searchBoundaryCandidates(3,
                [&](size_t depth) {
                    return CandidateChoices<int>{{1}, malformedDomain && depth == 1 ?
                        std::vector<size_t>{1} : std::vector<size_t>{}};
                },
                [&](size_t depth, int value) {
                    prefix.push_back(value);
                    ++pushes;
                    if (depth == 1) return CandidatePropagation::reject({depth + 1});
                    return CandidatePropagation::accept();
                },
                [&](size_t) { prefix.pop_back(); ++pops; },
                []() -> std::optional<int> { return 1; });
        };
        CHECK_THROWS_AS(run(), std::invalid_argument);
        CHECK(prefix.empty());
        CHECK(pops == pushes);
    }
}

TEST_CASE("explained candidates: final-check exceptions and unconditional failure unwind every choice") {
    for (bool throws : {false, true}) {
        std::vector<int> prefix;
        size_t pushes = 0, pops = 0;
        auto run = [&]() {
            return searchBoundaryCandidates(4,
                [](size_t) { return CandidateChoices<int>{{1}, {}}; },
                [&](size_t depth, int value) {
                    prefix.push_back(value);
                    ++pushes;
                    if (!throws && depth == 2) return CandidatePropagation::reject({});
                    return CandidatePropagation::accept();
                },
                [&](size_t) { prefix.pop_back(); ++pops; },
                []() -> std::optional<int> { throw std::runtime_error("final checker interrupted"); });
        };
        if (throws) CHECK_THROWS_AS(run(), std::runtime_error);
        else CHECK_FALSE(run().has_value());
        CHECK(prefix.empty());
        CHECK(pushes == pops);
    }
}

TEST_CASE("explained candidates: independent exhaustive Boolean oracle agrees with explained search") {
    std::mt19937 random(90071);
    for (size_t trial = 0; trial < 400; ++trial) {
        const size_t count = 1 + random() % 7;
        using Literal = std::pair<size_t, int>;
        std::vector<std::vector<Literal>> clauses(random() % 24);
        for (auto& clause : clauses)
            for (unsigned i = 0, length = 1 + random() % 4; i < length; ++i)
                clause.emplace_back(random() % count, random() % 2);
        if (trial % 19 == 0 && !clauses.empty()) clauses.front().clear();
        bool expected = false;
        for (size_t mask = 0; mask < (size_t(1) << count); ++mask) {
            bool all = true;
            for (const auto& clause : clauses) {
                bool any = false;
                for (const auto& [variable, value] : clause)
                    any |= static_cast<int>((mask >> variable) & 1) == value;
                all &= any;
            }
            expected |= all;
        }
        std::vector<int> prefix;
        size_t pushes = 0, pops = 0;
        const auto result = searchBoundaryCandidates(count,
            [](size_t) { return CandidateChoices<int>{{0, 1}, {}}; },
            [&](size_t depth, int value) {
                REQUIRE(prefix.size() == depth);
                prefix.push_back(value);
                ++pushes;
                for (const auto& clause : clauses) {
                    bool satisfied = false, pending = false;
                    std::vector<size_t> reasons;
                    for (const auto& [variable, literalValue] : clause) {
                        if (variable >= prefix.size()) pending = true;
                        else satisfied |= prefix[variable] == literalValue;
                        reasons.push_back(variable);
                    }
                    if (!pending && !satisfied) return CandidatePropagation::reject(std::move(reasons));
                }
                return CandidatePropagation::accept();
            },
            [&](size_t depth) {
                CHECK(prefix.size() == depth + 1);
                prefix.pop_back();
                ++pops;
            },
            [&]() -> std::optional<std::vector<int>> { return prefix; });
        REQUIRE(result.has_value() == expected);
        if (result) {
            for (const auto& clause : clauses) {
                bool satisfied = false;
                for (const auto& [variable, value] : clause) satisfied |= (*result)[variable] == value;
                CHECK(satisfied);
            }
        }
        CHECK(prefix.empty());
        CHECK(pushes == pops);
    }
}

TEST_CASE("explained candidates: empty domains and empty choice sequences use the final checker correctly") {
    size_t finalChecks = 0;
    auto complete = [&]() -> std::optional<int> { ++finalChecks; return 17; };
    const auto empty = searchBoundaryCandidates(0,
        [](size_t) { return CandidateChoices<int>{{}, {}}; },
        [](size_t, int) { return CandidatePropagation::accept(); }, [](size_t) {}, complete);
    REQUIRE(empty.has_value());
    CHECK(*empty == 17);
    CHECK(finalChecks == 1);
    const auto noDomain = searchBoundaryCandidates(1,
        [](size_t) { return CandidateChoices<int>{{}, {}}; },
        [](size_t, int) { return CandidatePropagation::accept(); }, [](size_t) {}, complete);
    CHECK_FALSE(noDomain.has_value());
    CHECK(finalChecks == 1);
}
