#include <doctest/doctest.h>
#include "search/candidate/BoundaryCandidates.h"
#include "search/candidate/CandidateDomains.h"
#include <random>
#include <stdexcept>

using namespace xolver;

TEST_CASE("explained candidates: checked partial completions unwind without filling unrelated choices") {
    for (const bool generationHint : {false, true}) {
        std::vector<int> prefix;
        size_t pushes = 0, pops = 0, checks = 0;
        const auto result = searchBoundaryCandidates(20,
            [&](size_t depth) { return CandidateChoices<int>{{1}, {}, generationHint && depth == 1}; },
            [&](size_t, int value) {
                prefix.push_back(value);
                ++pushes;
                return CandidatePropagation::accept(!generationHint);
            },
            [&](size_t) { prefix.pop_back(); ++pops; },
            [&]() -> std::optional<int> {
                ++checks;
                REQUIRE(prefix.size() == 1);
                return 17;
            });
        REQUIRE(result.has_value());
        CHECK(*result == 17);
        CHECK(pushes == 1);
        CHECK(pops == pushes);
        CHECK(checks == 1);
        CHECK(prefix.empty());
    }
}

TEST_CASE("explained candidates: unsuccessful partial completion continues search and interruption unwinds") {
    std::vector<int> prefix;
    const auto result = searchBoundaryCandidates(2,
        [](size_t) { return CandidateChoices<int>{{0, 1}, {}, true}; },
        [&](size_t, int value) { prefix.push_back(value); return CandidatePropagation::accept(true); },
        [&](size_t) { prefix.pop_back(); },
        [&]() -> std::optional<std::vector<int>> {
            if (prefix == std::vector<int>{1, 0}) return prefix;
            return std::nullopt;
        });
    REQUIRE(result.has_value());
    CHECK((*result == std::vector<int>{1, 0}));
    CHECK(prefix.empty());
    auto interrupted = [&]() {
        return searchBoundaryCandidates(4,
            [](size_t depth) { return CandidateChoices<int>{{1}, {}, depth == 1}; },
            [&](size_t, int value) { prefix.push_back(value); return CandidatePropagation::accept(); },
            [&](size_t) { prefix.pop_back(); },
            []() -> std::optional<int> { throw std::runtime_error("partial checker interrupted"); });
    };
    CHECK_THROWS_AS(interrupted(), std::runtime_error);
    CHECK(prefix.empty());
}

TEST_CASE("candidate domains: snapshots retain finite domains across refinement and owner destruction") {
    auto tick = []() {};
    const auto retained = [&]() {
        CandidateDomains<std::string> pool({{"a"}, {"lower", "upper"}});
        const auto first = pool.snapshot();
        CHECK(pool.suggest(0, "b", tick));
        CHECK_FALSE(pool.suggest(0, "a", tick));
        CHECK_FALSE(pool.suggest(0, "b", tick));
        CHECK((pool.snapshot().values(0) == std::vector<std::string>{"a"}));
        CHECK(pool.refine(tick) == 1);
        CHECK((first.values(0) == std::vector<std::string>{"a"}));
        CHECK((pool.snapshot().values(0) == std::vector<std::string>{"a", "b"}));
        CHECK(pool.refine(tick) == 0);
        CHECK_THROWS_AS(pool.suggest(2, "c", tick), std::out_of_range);
        return pool.snapshot();
    }();
    CHECK(retained.size() == 2);
    CHECK((retained.values(0) == std::vector<std::string>{"a", "b"}));
    CHECK((retained.values(1) == std::vector<std::string>{"lower", "upper"}));
}

TEST_CASE("candidate domains: interrupted refinement preserves publication and pending suggestions") {
    CandidateDomains<int> pool({{0}, {1}});
    auto tick = []() {};
    REQUIRE(pool.suggest(0, 2, tick));
    REQUIRE(pool.suggest(1, 3, tick));
    const auto first = pool.snapshot();
    int remaining = 3;
    auto interrupt = [&]() { if (--remaining == 0) throw std::runtime_error("allocation exhausted"); };
    CHECK_THROWS_AS(pool.refine(interrupt), std::runtime_error);
    CHECK((pool.snapshot().values(0) == std::vector<int>{0}));
    CHECK((pool.snapshot().values(1) == std::vector<int>{1}));
    CHECK_FALSE(pool.suggest(0, 2, tick));
    CHECK(pool.refine(tick) == 2);
    CHECK((pool.snapshot().values(0) == std::vector<int>{0, 2}));
    CHECK((pool.snapshot().values(1) == std::vector<int>{1, 3}));
    CHECK((first.values(0) == std::vector<int>{0}));
}

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
