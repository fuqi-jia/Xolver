#include <doctest/doctest.h>
#include "xolver/SeparationLogic.h"
#include "applications/sv/sl/HeapSearch.h"
#include <algorithm>
#include <functional>
#include <random>
using namespace xolver;
using namespace xolver::sl;

namespace {
FormulaId atLeast(Formula& f, unsigned count) {
    auto result = f.boolean(true);
    for (unsigned i = 0; i < count; ++i) {
        auto empty = f.emp();
        auto nonempty = f.negate(empty);
        result = f.star(nonempty, result);
    }
    return result;
}
void verdict(const Formula& f, Result expected) {
    auto answer = solve(f, {3000000, 256});
    INFO(answer.reason);
    REQUIRE((answer.result == expected));
    if (expected == Result::Sat) {
        auto checked = evaluate(f, answer.model, {3000000, 256});
        INFO(checked.reason);
        REQUIRE(checked.holds.has_value());
        CHECK(*checked.holds);
    }
}
}

TEST_CASE("SL Boolean heap: conjunction and star inspect different heaps") {
    Formula f({FieldSort::Integer});
    auto p = f.pointsTo(1, {std::string("2")});
    auto q = f.pointsTo(2, {std::string("3")});
    auto ne = f.relation(1, 2, false);
    auto both = f.conjunction(p, q);
    f.conjunction(ne, both);
    verdict(f, Result::Unsat);
    auto separate = f.star(p, q);
    f.conjunction(ne, separate);
    verdict(f, Result::Sat);
    f.conjunction(p, p);
    verdict(f, Result::Sat);
    f.star(p, p);
    verdict(f, Result::Unsat);
}

TEST_CASE("SL Boolean heap: negative star enumerates every partition") {
    // Regression shape from cvc5 issue #12913. On the two-cell heap the left
    // side of the equivalence is true (put an empty heap under not p); q is false.
    Formula f({FieldSort::Integer});
    auto p = f.pointsTo(1, {std::string("2")});
    auto q = f.pointsTo(2, {std::string("2")});
    auto heap = f.star(p, q);
    auto truth = f.boolean(true);
    auto notP = f.negate(p);
    auto l1 = f.star(notP, truth);
    auto left = f.star(l1, truth);
    auto both = f.conjunction(left, q);
    auto notLeft = f.negate(left);
    auto notQ = f.negate(q);
    auto neither = f.conjunction(notLeft, notQ);
    auto iff = f.disjunction(both, neither);
    f.conjunction(heap, iff);
    verdict(f, Result::Unsat);
}

TEST_CASE("SL Boolean heap: magic wand covers fresh data and fresh addresses") {
    Formula f({FieldSort::Integer});
    auto empty = f.emp();
    auto falsehood = f.boolean(false);
    auto truth = f.boolean(true);
    auto p = f.pointsTo(1, {std::string("7")});
    auto impossible = f.pointsTo(0, {std::string("7")});
    auto vacuous = f.wand(impossible, falsehood);
    f.negate(vacuous);
    verdict(f, Result::Unsat);
    auto extension = f.wand(truth, empty);
    verdict(f, Result::Unsat); // arbitrary fresh cells always extend the heap
    auto nonnil = f.relation(1, 0, false);
    auto blocked = f.wand(p, falsehood); // true precisely when x is allocated
    auto required = f.conjunction(nonnil, blocked);
    f.conjunction(required, empty);
    verdict(f, Result::Unsat);
    f.conjunction(required, p);
    verdict(f, Result::Sat);
    auto identity = f.wand(empty, p);
    auto notP = f.negate(p);
    f.conjunction(identity, notP);
    verdict(f, Result::Unsat);
    // Empty heap entails that every non-p cell can be added. A record different
    // from every literal in the formula is essential to falsify this wand.
    auto notCell = f.negate(p);
    auto onlyP = f.wand(notCell, empty);
    f.conjunction(empty, onlyP);
    verdict(f, Result::Unsat);
    auto pointer = f.wand(p, p);
    f.conjunction(empty, pointer);
    verdict(f, Result::Sat);
    auto vacuousInner = f.wand(falsehood, p);
    f.wand(vacuousInner, p);
    verdict(f, Result::Unsat); // formally proved in proofs/SeparationLogic.v
}

TEST_CASE("SL Boolean heap: anonymous cardinality is formula-derived") {
    for (unsigned count = 1; count <= 5; ++count) {
        Formula f;
        auto lower = atLeast(f, count);
        auto upper = atLeast(f, count + 1);
        auto belowUpper = f.negate(upper);
        f.conjunction(lower, belowUpper);
        auto answer = solve(f, {3000000, 256});
        REQUIRE((answer.result == Result::Sat));
        CHECK(answer.model.heap.size() == count);
        auto checked = evaluate(f, answer.model, {3000000, 256});
        REQUIRE(checked.holds.has_value());
        CHECK(*checked.holds);
        answer.model.heap.erase(answer.model.heap.begin());
        CHECK(evaluate(f, answer.model, {3000000, 256}).holds == std::optional<bool>(false));
    }
}

TEST_CASE("SL Boolean heap: wand distinguishes fresh records from a singleton data sort") {
    for (bool integerField : {false, true}) {
        Formula f(integerField ? std::vector{FieldSort::Integer} : std::vector<FieldSort>{});
        auto p = f.pointsTo(1, integerField ? std::vector<Field>{std::string("7")}
                                           : std::vector<Field>{});
        auto falsehood = f.boolean(false);
        auto allocated = f.wand(p, falsehood);
        auto empty = f.emp();
        auto nonempty = f.negate(empty);
        auto atLeastTwo = f.star(nonempty, nonempty);
        auto atMostOne = f.negate(atLeastTwo);
        auto singletonAtX = f.conjunction(allocated, atMostOne);
        auto everyRecordIsP = f.wand(singletonAtX, p);
        auto nonnil = f.relation(1, 0, false);
        auto premise = f.conjunction(empty, nonnil);
        f.conjunction(premise, everyRecordIsP);
        // Int permits an unmentioned value at x, refuting the universal claim.
        // The empty record has exactly one value, so the same claim is true.
        verdict(f, integerField ? Result::Unsat : Result::Sat);
    }
}

TEST_CASE("SL Boolean heap: alias partitions and typed records") {
    Formula f({FieldSort::Location, FieldSort::Integer});
    auto p = f.pointsTo(1, {Location{2}, std::string("0007")});
    auto q = f.pointsTo(3, {Location{4}, std::string("7")});
    auto sameHeap = f.conjunction(p, q);
    auto differentFields = f.relation(2, 4, false);
    f.conjunction(sameHeap, differentFields);
    verdict(f, Result::Unsat);
    f.root = sameHeap;
    auto answer = solve(f);
    REQUIRE((answer.result == Result::Sat));
    CHECK(answer.model.locations.at(1) == answer.model.locations.at(3));
    CHECK(answer.model.locations.at(2) == answer.model.locations.at(4));
    answer.model.heap.begin()->second[1] = std::string("-7");
    CHECK(evaluate(f, answer.model).holds == std::optional<bool>(false));

    Formula unit(std::vector<FieldSort>{});
    auto cell = unit.pointsTo(1, {});
    auto empty = unit.emp();
    auto truth = unit.boolean(true);
    auto allocated = unit.star(cell, truth);
    auto notAllocated = unit.negate(allocated);
    auto noCell = unit.negate(cell);
    auto everyCell = unit.wand(noCell, noCell);
    auto negation = unit.negate(everyCell);
    // At the empty heap A -* A is true even for the singleton data domain.
    unit.conjunction(empty, negation);
    verdict(unit, Result::Unsat);
    unit.conjunction(notAllocated, cell);
    verdict(unit, Result::Unsat);
}

TEST_CASE("SL Boolean heap: malformed evidence and limits stay unknown") {
    Formula f({FieldSort::Integer});
    f.pointsTo(1, {std::string("1/2")});
    CHECK((solve(f).result == Result::Unknown));
    f.nodes.back().cell.fields = {Location{2}};
    CHECK((solve(f).result == Result::Unknown));
    f.nodes.back().cell.fields = {std::string("1")};
    auto answer = solve(f);
    REQUIRE((answer.result == Result::Sat));
    auto missing = answer.model;
    missing.locations.erase(1);
    CHECK_FALSE(evaluate(f, missing).holds.has_value());
    auto nil = answer.model;
    nil.heap[0] = {std::string("1")};
    CHECK_FALSE(evaluate(f, nil).holds.has_value());
    CHECK((solve(f, {0, 256}).result == Result::Unknown));
    CHECK_FALSE(evaluate(f, answer.model, {0, 256}).holds.has_value());
    CHECK((solve(f, {100, 0}).result == Result::Unknown));
    auto id = f.negate(f.root);
    f.nodes[id].children[0] = id;
    CHECK((solve(f).result == Result::Unknown));
}

TEST_CASE("SL Boolean heap: unreachable symbols do not multiply stack partitions") {
    Formula f({FieldSort::Integer});
    for (Location i = 1; i <= 1000; ++i) f.pointsTo(i, {std::to_string(i)});
    f.boolean(false);
    auto answer = solve(f, {20000, 256});
    INFO(answer.reason);
    CHECK((answer.result == Result::Unsat));
    f.boolean(true);
    answer = solve(f, {20000, 256});
    REQUIRE((answer.result == Result::Sat));
    CHECK(answer.model.locations.size() == 1); // only nil is relevant
    CHECK(answer.model.heap.empty());
}

TEST_CASE("SL Boolean heap: fixed stack preserves supplied addresses and records") {
    Formula f({FieldSort::Location});
    f.pointsTo(1, {Location{2}});
    detail::Work work{{100000, 256}};
    auto prepared = detail::prepare(f, work);
    const std::map<Location, uint64_t> stack{{0, 0}, {1, 41}, {2, 9001}};
    auto answer = detail::solveHeap(prepared, stack, work);
    REQUIRE((answer.result == Result::Sat));
    CHECK(answer.model.locations == stack);
    REQUIRE(answer.model.heap.size() == 1);
    CHECK(answer.model.heap.at(41) == std::vector<ConcreteField>{uint64_t{9001}});
    CHECK(evaluate(f, answer.model).holds == std::optional<bool>(true));

    auto nil = stack;
    nil.at(1) = 0;
    CHECK((detail::solveHeap(prepared, nil, work).result == Result::Unsat));
    // This UNSAT concerns the supplied stack; the existential query is SAT.
    CHECK((solve(f).result == Result::Sat));

    auto missing = stack;
    missing.erase(2);
    CHECK_THROWS_AS(detail::solveHeap(prepared, missing, work), detail::Stop);
    auto invalidNil = stack;
    invalidNil.at(0) = 1;
    CHECK_THROWS_AS(detail::solveHeap(prepared, invalidNil, work), detail::Stop);
}

TEST_CASE("SL Boolean heap: fixed stack controls universal heap extensions") {
    Formula f({FieldSort::Integer});
    const auto p = f.pointsTo(1, {std::string("7")});
    const auto q = f.pointsTo(2, {std::string("7")});
    const auto implication = f.wand(p, q);
    const auto empty = f.emp();
    f.conjunction(empty, implication);
    detail::Work work{{1000000, 256}};
    auto prepared = detail::prepare(f, work);
    for (uint64_t a : {0, 17, 91}) for (uint64_t b : {0, 17, 91}) {
        INFO(a, ", ", b);
        const std::map<Location, uint64_t> stack{{0, 0}, {1, a}, {2, b}};
        auto answer = detail::solveHeap(prepared, stack, work);
        const auto expected = a == 0 || a == b ? Result::Sat : Result::Unsat;
        CHECK((answer.result == expected));
        if (answer.result == Result::Sat) {
            CHECK(answer.model.locations == stack);
            CHECK(answer.model.heap.empty());
        }
    }
}

TEST_CASE("SL Boolean heap: data-only values do not multiply allocation sites") {
    Formula f({FieldSort::Location});
    f.pointsTo(1, {Location{2}});
    std::map<Location, uint64_t> stack{{0, 0}, {1, 1001}, {2, 2}};
    for (Location i = 3; i <= 40; ++i) {
        auto root = f.root;
        auto identity = f.relation(i, i);
        f.conjunction(root, identity);
        stack.emplace(i, i);
    }
    detail::Work work{{100000, 256}};
    auto prepared = detail::prepare(f, work);
    auto answer = detail::solveHeap(prepared, stack, work);
    INFO(answer.reason);
    REQUIRE((answer.result == Result::Sat));
    REQUIRE(answer.model.heap.size() == 1);
    CHECK(answer.model.heap.count(1001) == 1);
    CHECK(evaluate(f, answer.model).holds == std::optional<bool>(true));
}

TEST_CASE("SL Boolean heap: fixed stack searches and witness checks share one budget") {
    Formula f;
    f.emp();
    const std::map<Location, uint64_t> stack{{0, 0}};
    detail::Work measured{{100000, 256}};
    auto prepared = detail::prepare(f, measured);
    const auto preparation = measured.steps;
    auto answer = detail::solveHeap(prepared, stack, measured);
    REQUIRE((answer.result == Result::Sat));
    const auto cost = measured.steps - preparation;
    const auto checking = evaluate(f, answer.model).steps;
    CHECK(cost >= checking);

    detail::Work shared{{preparation + 2 * cost, 256}};
    prepared = detail::prepare(f, shared);
    CHECK((detail::solveHeap(prepared, stack, shared).result == Result::Sat));
    CHECK((detail::solveHeap(prepared, stack, shared).result == Result::Sat));
    CHECK(shared.steps == shared.limits.maxSteps);
    CHECK_THROWS_AS(detail::solveHeap(prepared, stack, shared), detail::Stop);

    // A budget that cannot cover the independent witness check cannot publish
    // SAT, even when heap search itself has already found the empty heap.
    detail::Work shortBudget{{preparation + cost - 1, 256}};
    prepared = detail::prepare(f, shortBudget);
    CHECK((detail::solveHeap(prepared, stack, shortBudget).result == Result::Unknown));
}

TEST_CASE("SL Boolean heap: wand adjunction and distribution laws") {
    // Universal validity of algebraic laws, checked by UNSAT of the negation.
    Formula f({FieldSort::Integer});
    auto p = f.pointsTo(1, {std::string("1")});
    auto q = f.pointsTo(2, {std::string("2")});
    auto truth = f.boolean(true);
    auto openP = f.star(p, truth);
    auto openQ = f.star(q, truth);
    auto pq = f.star(openP, openQ);
    auto implication = f.wand(openP, pq);
    auto bad = f.negate(implication);
    f.conjunction(openQ, bad); // Q entails P -* (P * Q)
    verdict(f, Result::Unsat);
    auto andPQ = f.conjunction(p, q);
    auto wandAnd = f.wand(truth, andPQ);
    auto wp = f.wand(truth, p);
    auto wq = f.wand(truth, q);
    auto both = f.conjunction(wp, wq);
    auto notBoth = f.negate(both);
    auto notWandAnd = f.negate(wandAnd);
    auto d1 = f.conjunction(wandAnd, notBoth);
    auto d2 = f.conjunction(both, notWandAnd);
    f.disjunction(d1, d2);
    verdict(f, Result::Unsat);
    auto curriedInner = f.wand(openQ, p);
    auto curried = f.wand(openP, curriedInner);
    auto uncurried = f.wand(pq, p);
    auto notCurried = f.negate(curried);
    auto notUncurried = f.negate(uncurried);
    auto c1 = f.conjunction(curried, notUncurried);
    auto c2 = f.conjunction(uncurried, notCurried);
    f.disjunction(c1, c2);
    verdict(f, Result::Unsat);
}

TEST_CASE("SL Boolean heap: randomized Boolean formulas agree with concrete semantics") {
    // Exhaust every stack for two symbols and every heap over the two non-nil
    // named values plus four fresh cells. Generated widths <=3, making the oracle
    // complete for these wand-free cases. It uses concrete partition semantics.
    std::mt19937 rng(50441);
    for (unsigned trial = 0; trial < 80; ++trial) {
        Formula f(std::vector<FieldSort>{});
        f.emp(); f.pointsTo(1, {}); f.pointsTo(2, {});
        f.relation(1, 2); f.boolean(true);
        std::vector<unsigned> width{1, 1, 1, 0, 0};
        for (unsigned j = 0; j < 3; ++j) {
            const auto a = rng() % f.nodes.size(), b = rng() % f.nodes.size();
            unsigned next = std::max(width[a], width[b]);
            switch (rng() % 4) {
            case 0: f.negate(a); next = width[a]; break;
            case 1: f.conjunction(a, b); break;
            case 2: f.disjunction(a, b); break;
            case 3:
                if (width[a] + width[b] > 3) f.conjunction(a, b);
                else { f.star(a, b); next = width[a] + width[b]; }
                break;
            }
            width.push_back(next);
        }
        bool exists = false;
        detail::Work work{{3000000, 256}};
        auto prepared = detail::prepare(f, work);
        for (uint64_t a = 0; a <= 2; ++a)
            for (uint64_t b = 0; b <= 2; ++b) {
                bool stackExists = false;
                for (unsigned mask = 0; mask < 64 && !stackExists; ++mask) {
                    Model m{{{0, 0}, {1, a}, {2, b}}, {}};
                    for (unsigned k = 0; k < 6; ++k)
                        if ((mask >> k) & 1) m.heap.emplace(k + 1, std::vector<ConcreteField>{});
                    auto checked = evaluate(f, m);
                    REQUIRE(checked.holds.has_value());
                    stackExists = *checked.holds;
                }
                const auto expected = stackExists ? Result::Sat : Result::Unsat;
                auto answer = detail::solveHeap(prepared, {{0, 0}, {1, a}, {2, b}}, work);
                INFO("trial ", trial, ", stack ", a, ", ", b, ": ", answer.reason);
                CHECK((answer.result == expected));
                exists = exists || stackExists;
            }
        verdict(f, exists ? Result::Sat : Result::Unsat);
    }
}
