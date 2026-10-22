#include <doctest/doctest.h>
#include "xolver/SeparationLogic.h"
#include <array>
#include <random>
using namespace xolver;
using namespace xolver::sl;

TEST_CASE("symbolic heap: exact emp and typed points-to witnesses") {
    SymbolicHeap empty;
    auto emp = solve(empty);
    REQUIRE((emp.result == Result::Sat));
    CHECK(checkModel(empty, emp.model));
    emp.model.heap[1] = {};
    CHECK_FALSE(checkModel(empty, emp.model));
    SymbolicHeap query{{{1, 3, true}}, {
        {1, {Location{2}, std::string("100000000000000000000000000000000000000")}},
        {2, {Location{0}, std::string("-17")}}}};
    auto result = solve(query);
    REQUIRE((result.result == Result::Sat));
    CHECK(result.model.locations.at(1) == result.model.locations.at(3));
    CHECK(checkModel(query, result.model));
    auto bad = result.model;
    bad.locations[2] = bad.locations[1];
    CHECK_FALSE(checkModel(query, bad));
    query.spatial[0].fields[1] = std::string("2/3");
    CHECK((solve(query).result == Result::Unknown));
}

TEST_CASE("symbolic heap: conflict proofs are bound to actual premises") {
    SymbolicHeap query{{{1, 2, true}, {3, 2, true}}, {{1, {}}, {3, {}}}};
    auto result = solve(query);
    REQUIRE((result.result == Result::Unsat));
    REQUIRE(result.conflict.has_value());
    CHECK(checkConflict(query, *result.conflict));
    auto corrupt = *result.conflict;
    corrupt.path[0].premise = 100;
    CHECK_FALSE(checkConflict(query, corrupt));
    corrupt = *result.conflict;
    corrupt.second = corrupt.first;
    CHECK_FALSE(checkConflict(query, corrupt));
    query.pure[1].equal = false;
    CHECK_FALSE(checkConflict(query, *result.conflict));
    CHECK((solve(query).result == Result::Sat));
}

TEST_CASE("symbolic heap: null allocation and pure contradictions have certificates") {
    for (auto query : {
        SymbolicHeap{{{1, 0, true}}, {{1, {}}}},
        SymbolicHeap{{{1, 2, true}, {2, 3, true}, {1, 3, false}}, {}},
        SymbolicHeap{{}, {{0, {}}}},
        SymbolicHeap{{}, {{1, {}}, {1, {}}}}
    }) {
        auto result = solve(query);
        REQUIRE((result.result == Result::Unsat));
        REQUIRE(result.conflict.has_value());
        CHECK(checkConflict(query, *result.conflict));
    }
}

TEST_CASE("symbolic heap: random formulas agree with exhaustive finite valuations") {
    // Four location symbols plus nil need at most five distinct locations.
    // Enumerating that finite domain is therefore complete for this fragment.
    std::mt19937 random(7549);
    for (int trial = 0; trial < 200; ++trial) {
        SymbolicHeap query;
        for (int i = 0; i < 6; ++i)
            query.pure.push_back({Location(random() % 5), Location(random() % 5), bool(random() % 2)});
        const int cells = random() % 5;
        for (int i = 0; i < cells; ++i) query.spatial.push_back({Location(random() % 5), {}});
        bool exists = false;
        for (int assignment = 0; assignment < 625 && !exists; ++assignment) {
            std::array<int, 5> values{0, 0, 0, 0, 0};
            int digits = assignment;
            for (int i = 1; i < 5; ++i) { values[i] = digits % 5; digits /= 5; }
            bool valid = true;
            for (const auto& c : query.pure)
                valid &= (values[c.left] == values[c.right]) == c.equal;
            for (std::size_t i = 0; i < query.spatial.size(); ++i) {
                valid &= values[query.spatial[i].address] != 0;
                for (std::size_t j = 0; j < i; ++j)
                    valid &= values[query.spatial[i].address] != values[query.spatial[j].address];
            }
            exists |= valid;
        }
        auto answer = solve(query);
        REQUIRE((answer.result == (exists ? Result::Sat : Result::Unsat)));
        if (exists) CHECK(checkModel(query, answer.model));
        else { REQUIRE(answer.conflict.has_value()); CHECK(checkConflict(query, *answer.conflict)); }
    }
}
