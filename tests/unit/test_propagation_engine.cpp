#include <doctest/doctest.h>
#include "search/lra/LraPropagationEngine.h"
#include "search/lra/GeneralSimplex.h"
#include <algorithm>
#include <chrono>
#include <thread>
#include <stdexcept>
#include <utility>

using namespace xolver;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static BoundInfo mkBound(const mpq_class& val, SatVar sv) {
    return BoundInfo(BoundValue(DeltaRational(val)), SatLit{sv, true});
}

static bool hasBound(const std::vector<LraPropagationEngine::ExplainedBound>& bounds,
                     int var, bool isLower, const mpq_class& expected) {
    for (const auto& b : bounds) {
        if (b.var == var && b.isLower == isLower && b.value.a == expected && b.value.b == 0) {
            return true;
        }
    }
    return false;
}

static int countBounds(const std::vector<LraPropagationEngine::ExplainedBound>& bounds,
                       int var, bool isLower) {
    int c = 0;
    for (const auto& b : bounds) {
        if (b.var == var && b.isLower == isLower) ++c;
    }
    return c;
}

static void checkPropagationPoint(const std::vector<LraPropagationEngine::ExplainedBound>& bounds,
                                  const std::vector<mpq_class>& point) {
    for (const auto& bound : bounds) {
        REQUIRE(bound.var >= 0);
        REQUIRE(static_cast<std::size_t>(bound.var) < point.size());
        const DeltaRational value(point[bound.var]);
        CHECK((bound.isLower ? value >= bound.value : value <= bound.value));
    }
}

TEST_CASE("LraPropagationEngine: retained rows reuse arithmetic after unrelated changes") {
    GeneralSimplex gs;
    const int x = gs.addVar("reuse-x"), y = gs.addVar("reuse-y"), z = gs.addVar("reuse-z");
    const int s = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    const int t = gs.addConstraint({{z, 2}}, 0);
    REQUIRE(gs.assertLower(x, mkBound(1, 1)));
    REQUIRE(gs.assertLower(y, mkBound(2, 2)));
    REQUIRE(gs.assertLower(z, mkBound(4, 3)));
    LraPropagationEngine engine;
    LraPropagationEngine::Statistics first, repeated, changed;
    const PropagationBudget budget{64, 256, 12, 1000};
    CHECK(hasBound(engine.propagateAll(gs, budget, &first), s, true, 3));
    CHECK(first.termPairs > 0);
    CHECK(hasBound(engine.propagateAll(gs, budget, &repeated), s, true, 3));
    CHECK(repeated.retainedSnapshotHits > 0);
    CHECK(repeated.termPairs == 0);
    CHECK(repeated.changedInputs == 0);
    REQUIRE(gs.assertLower(z, mkBound(5, 4)));
    const auto result = engine.propagateAll(gs, budget, &changed);
    CHECK(hasBound(result, s, true, 3));
    CHECK(hasBound(result, t, true, 10));
    CHECK(changed.changedInputs == 1);
    CHECK(changed.retainedSnapshotHits > 0);
    CHECK(changed.termPairs < first.termPairs);
    checkPropagationPoint(result, {1, 2, 5, 3, 10});
    auto copied = engine;
    LraPropagationEngine::Statistics copyWork;
    CHECK(hasBound(copied.propagateAll(gs, budget, &copyWork), s, true, 3));
    CHECK(copyWork.retainedSnapshotHits == 0);
    auto moved = std::move(copied);
    CHECK(hasBound(moved.propagateAll(gs, budget), t, true, 10));
    CHECK(hasBound(copied.propagateAll(gs, budget), t, true, 10));
}

TEST_CASE("LraPropagationEngine: retained rows expire transitive premises with reused literals") {
    GeneralSimplex gs;
    const int x = gs.addVar("premise-x"), y = gs.addVar("premise-y"), z = gs.addVar("premise-z");
    const int s = gs.addConstraint({{x, 1}, {y, -1}}, 0);
    const int t = gs.addConstraint({{y, 1}, {z, 1}}, 0);
    auto install = [&](int lower) {
        gs.resetActiveBounds();
        REQUIRE(gs.assertLower(s, mkBound(lower, 1)));
        REQUIRE(gs.assertUpper(x, mkBound(2, 2)));
        REQUIRE(gs.assertUpper(z, mkBound(3, 3)));
    };
    LraPropagationEngine engine;
    const PropagationBudget budget{64, 256, 12, 1000};
    install(1);
    CHECK(hasBound(engine.propagateAll(gs, budget), t, false, 4));
    CHECK(hasBound(engine.propagateAll(gs, budget), t, false, 4));
    // s has an empty column: invalidating only incident rows misses t's cached
    // y <= 1 contribution, whose premise came from another row.
    REQUIRE(gs.tableau().col(s).entries.empty());
    install(-10);
    const auto weakened = engine.propagateAll(gs, budget);
    CHECK(hasBound(weakened, y, false, 12));
    CHECK(hasBound(weakened, t, false, 15));
    CHECK_FALSE(hasBound(weakened, t, false, 4));
    checkPropagationPoint(weakened, {2, 12, 3, -10, 15});
    gs.resetActiveBounds();
    REQUIRE(gs.assertUpper(x, mkBound(2, 2)));
    REQUIRE(gs.assertUpper(z, mkBound(3, 3)));
    const auto removed = engine.propagateAll(gs, budget);
    CHECK_FALSE(hasBound(removed, y, false, 12));
    checkPropagationPoint(removed, {2, 100, 3, -98, 103});
}

TEST_CASE("LraPropagationEngine: retained rows cannot cross reset or simplex assignment") {
    GeneralSimplex gs;
    auto install = [](GeneralSimplex& target, int coefficient) {
        const int x = target.addVar("identity-x"), y = target.addVar("identity-y");
        const int s = target.addConstraint({{x, 1}, {y, coefficient}}, 0);
        REQUIRE(s == 2);
        REQUIRE(target.assertLower(x, mkBound(1, 1)));
        REQUIRE(target.assertLower(y, mkBound(2, 2)));
    };
    install(gs, 1);
    LraPropagationEngine engine;
    const PropagationBudget budget{64, 256, 12, 1000};
    CHECK(hasBound(engine.propagateAll(gs, budget), 2, true, 3));
    const auto before = gs.definitionIdentity();
    gs.reset();
    install(gs, -1);
    CHECK(gs.definitionIdentity() != before);
    checkPropagationPoint(engine.propagateAll(gs, budget), {1, 100, -99});
    GeneralSimplex replacement;
    install(replacement, 1);
    gs = replacement;
    CHECK(gs.definitionIdentity() != replacement.definitionIdentity());
    CHECK(hasBound(engine.propagateAll(gs, budget), 2, true, 3));
    replacement.reset();
    install(replacement, -1);
    gs = std::move(replacement);
    checkPropagationPoint(engine.propagateAll(gs, budget), {1, 100, -99});
}

TEST_CASE("LraPropagationEngine: retained rows survive pivots and append definitions safely") {
    GeneralSimplex gs;
    const int x = gs.addVar("pivot-cache-x"), y = gs.addVar("pivot-cache-y");
    const int s = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    REQUIRE(gs.assertLower(x, mkBound(0, 1)));
    REQUIRE(gs.assertLower(y, mkBound(0, 2)));
    LraPropagationEngine engine;
    const PropagationBudget budget{64, 256, 12, 1000};
    CHECK(hasBound(engine.propagateAll(gs, budget), s, true, 0));
    gs.push();
    REQUIRE(gs.assertLower(s, mkBound(5, 3), 1));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    CHECK(gs.basicRowOfVar(s) < 0);
    checkPropagationPoint(engine.propagateAll(gs, budget), {2, 3, 5});
    gs.pop();
    checkPropagationPoint(engine.propagateAll(gs, budget), {0, 0, 0});
    const auto identity = gs.definitionIdentity();
    const int t = gs.addConstraint({{x, 2}, {y, -1}}, 0);
    CHECK(gs.definitionIdentity() == identity);
    CHECK(t == 3);
    checkPropagationPoint(engine.propagateAll(gs, budget), {0, 0, 0, 0});
    SparseRow saturated;
    saturated.version = std::numeric_limits<uint64_t>::max();
    saturated.noteChange();
    CHECK(saturated.version == std::numeric_limits<uint64_t>::max());
}

TEST_CASE("LraPropagationEngine: retained rows obey budgets and discard throwing consumers") {
    GeneralSimplex gs;
    const int x = gs.addVar("throw-cache-x");
    const int s = gs.addConstraint({{x, 2}}, 0);
    REQUIRE(gs.assertLower(x, mkBound(1, 1)));
    LraPropagationEngine engine;
    const PropagationBudget budget{64, 256, 12, 1000};
    CHECK(hasBound(engine.propagateAll(gs, budget), s, true, 2));
    CHECK(engine.propagateAll(gs, {0, 256, 12, 1000}).empty());
    CHECK(engine.propagateAll(gs, {64, 0, 12, 1000}).empty());
    CHECK(engine.propagateAll(gs, {64, 256, 12, 0}).empty());
    CHECK(engine.propagateAll(gs, {64, 256, 0, 1000}).empty());
    CHECK_THROWS_AS(engine.propagateAll(gs, budget, nullptr,
        [](const auto&) -> bool { throw std::runtime_error("consumer failure"); }), std::runtime_error);
    LraPropagationEngine::Statistics after;
    CHECK(hasBound(engine.propagateAll(gs, {1, 256, 12, 1000}, &after), s, true, 2));
    CHECK(after.retainedSnapshotHits == 0);
    CHECK(after.rowSnapshots == 1);
}

TEST_CASE("LraPropagationEngine: unavailable extrema skip arithmetic until bounds arrive") {
    GeneralSimplex gs;
    const int x = gs.addVar("availability-x"), y = gs.addVar("availability-y"), z = gs.addVar("availability-z");
    const int s = gs.addConstraint({{x, 1}, {y, -2}, {z, 3}}, 0);
    REQUIRE(gs.assertLower(s, mkBound(0, 1)));
    REQUIRE(gs.assertUpper(s, mkBound(0, 2)));
    LraPropagationEngine engine;
    auto checkUnavailable = [&] {
        LraPropagationEngine::Statistics statistics;
        CHECK(engine.propagateAll(gs, {64, 256, 12, 1000}, &statistics).empty());
        CHECK(statistics.rowVisits == 2);
        CHECK(statistics.rowSnapshots == 1);
        CHECK(statistics.snapshotHits == 1);
        CHECK(statistics.unproductiveSnapshots == 1);
        CHECK(statistics.termPairs == 0);
    };
    checkUnavailable();
    gs.push();
    REQUIRE(gs.assertUpper(x, BoundInfo(BoundValue(DeltaRational(4, -1)), SatLit::positive(3)), 1));
    REQUIRE(gs.assertUpper(z, mkBound(2, 4), 1));
    // Only the maximum is now available after excluding y. The unavailable
    // minimum must not suppress 0 <= x-2y+3z => y < 5.
    const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000});
    const auto found = std::find_if(derived.begin(), derived.end(), [y](const auto& bound) {
        return bound.var == y && !bound.isLower &&
            bound.value == DeltaRational(5, mpq_class(-1, 2));
    });
    REQUIRE(found != derived.end());
    CHECK((found->reasons == std::vector<SatLit>{SatLit::positive(1), SatLit::positive(3), SatLit::positive(4)}));
    CHECK_FALSE(gs.varState(y).upper.bound.isFinite());
    gs.pop();
    checkUnavailable();
}

TEST_CASE("LraPropagationEngine: skipped rows are revisited by local closure") {
    GeneralSimplex gs;
    const int x = gs.addVar("availability-chain-x"), y = gs.addVar("availability-chain-y"), z = gs.addVar("availability-chain-z");
    const int target = gs.addConstraint({{x, 1}, {y, 1}, {z, 1}}, 0);
    const int first = gs.addConstraint({{x, 1}}, 0);
    const int second = gs.addConstraint({{y, 1}}, 0);
    REQUIRE(gs.assertUpper(target, mkBound(6, 1)));
    REQUIRE(gs.assertLower(first, mkBound(1, 2)));
    REQUIRE(gs.assertLower(second, mkBound(2, 3)));
    LraPropagationEngine engine;
    LraPropagationEngine::Statistics statistics;
    const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000}, &statistics);
    CHECK(statistics.unproductiveSnapshots > 0);
    const auto found = std::find_if(derived.begin(), derived.end(), [z](const auto& bound) {
        return bound.var == z && !bound.isLower && bound.value == DeltaRational(3);
    });
    REQUIRE(found != derived.end());
    CHECK((found->reasons == std::vector<SatLit>{SatLit::positive(1), SatLit::positive(2), SatLit::positive(3)}));
    CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(y).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(z).upper.bound.isFinite());
}

TEST_CASE("LraPropagationEngine: a full consumer stops before unused rows") {
    GeneralSimplex gs;
    for (int row = 0; row < 8; ++row) {
        const int x = gs.addVar("consumer-x" + std::to_string(row));
        const int s = gs.addConstraint({{x, 1}}, 0);
        REQUIRE(gs.assertLower(s, mkBound(-20 + row, 2 * row + 1)));
        REQUIRE(gs.assertUpper(s, mkBound(20 + row, 2 * row + 2)));
    }
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    const PropagationBudget budget{64, 256, 12, 1000};
    LraPropagationEngine batch, streaming;
    LraPropagationEngine::Statistics completeWork, stoppedWork;
    const auto complete = batch.propagateAll(gs, budget, &completeWork);
    REQUIRE(complete.size() == 16);
    std::vector<LraPropagationEngine::ExplainedBound> consumed;
    const auto prefix = streaming.propagateAll(gs, budget, &stoppedWork,
        [&](const auto& bound) {
            consumed.push_back(bound);
            return consumed.size() < 3;
        });
    REQUIRE(prefix.size() == 3);
    REQUIRE(consumed.size() == prefix.size());
    for (std::size_t i = 0; i < prefix.size(); ++i) {
        CHECK(prefix[i].var == complete[i].var);
        CHECK(prefix[i].isLower == complete[i].isLower);
        CHECK(prefix[i].value == complete[i].value);
        CHECK(prefix[i].reasons == complete[i].reasons);
        CHECK(consumed[i].var == prefix[i].var);
        CHECK(consumed[i].value == prefix[i].value);
        CHECK(consumed[i].reasons == prefix[i].reasons);
    }
    CHECK(stoppedWork.rowVisits < completeWork.rowVisits);
    CHECK(stoppedWork.termPairs < completeWork.termPairs);
    // Stopping is local to the invocation; it does not latch the engine off.
    const auto resumed = streaming.propagateAll(gs, budget);
    REQUIRE_FALSE(resumed.empty());
    CHECK(resumed.front().var == complete[3].var);
    CHECK(resumed.front().isLower == complete[3].isLower);
}

TEST_CASE("LraPropagationEngine: consumer stop keeps exact bounds local across rollback") {
    GeneralSimplex gs;
    const int x = gs.addVar("consumer-rollback-x");
    const int s = gs.addConstraint({{x, -2}}, 0);
    REQUIRE(gs.assertLower(s, mkBound(-6, 101)));
    REQUIRE(gs.assertUpper(s, mkBound(6, 102)));
    LraPropagationEngine engine;
    auto checkCurrent = [&](bool child) {
        std::vector<bool> sides(2, false);
        for (int call = 0; call < 2; ++call) {
            int deliveries = 0;
            const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000}, nullptr,
                [&](const auto&) { ++deliveries; return false; });
            REQUIRE(derived.size() == 1);
            CHECK(deliveries == 1);
            const auto& bound = derived.front();
            CHECK(bound.var == x);
            CHECK(bound.value == (bound.isLower ? DeltaRational(-3) :
                child ? DeltaRational(mpq_class(1, 2), mpq_class(-1, 2)) : DeltaRational(3)));
            REQUIRE(bound.reasons.size() == 1);
            CHECK(bound.reasons.front() == SatLit::positive(bound.isLower ? 102 : child ? 103 : 101));
            sides[bound.isLower ? 0 : 1] = true;
        }
        CHECK(sides[0]);
        CHECK(sides[1]);
        CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
        CHECK_FALSE(gs.varState(x).upper.bound.isFinite());
    };
    checkCurrent(false);
    gs.push();
    REQUIRE(gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(-1, 1)), SatLit::positive(103)), 1));
    checkCurrent(true);
    gs.pop();
    checkCurrent(false);
}

TEST_CASE("LraPropagationEngine: consumer latency does not spend the arithmetic budget") {
    GeneralSimplex gs;
    const int x = gs.addVar("consumer-budget-x");
    const int s = gs.addConstraint({{x, 1}}, 0);
    REQUIRE(gs.assertLower(s, mkBound(-3, 1)));
    REQUIRE(gs.assertUpper(s, mkBound(3, 2)));
    LraPropagationEngine engine;
    int deliveries = 0;
    const auto derived = engine.propagateAll(gs, {2, 16, 12, 100}, nullptr,
        [&](const auto&) {
            ++deliveries;
            std::this_thread::sleep_for(std::chrono::milliseconds(120));
            return true;
        });
    CHECK(deliveries == 2);
    CHECK(hasBound(derived, x, true, -3));
    CHECK(hasBound(derived, x, false, 3));
    CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(x).upper.bound.isFinite());
}

TEST_CASE("LraPropagationEngine: bounded repeated checks reach every row direction") {
    for (bool boundLimited : {false, true}) {
        CAPTURE(boundLimited);
        GeneralSimplex gs;
        std::vector<int> variables;
        for (int row = 0; row < 13; ++row) {
            const int x = gs.addVar("fair-x" + std::to_string(row));
            variables.push_back(x);
            const int s = gs.addConstraint({{x, 1}}, 0);
            REQUIRE(gs.assertLower(s, mkBound(-20 + row, 2 * row + 1)));
            REQUIRE(gs.assertUpper(s, mkBound(20 + row, 2 * row + 2)));
        }
        REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
        LraPropagationEngine engine;
        std::vector<bool> reached(26, false);
        const PropagationBudget budget{boundLimited ? 1 : 64, boundLimited ? 2 : 1, 12, 1000};
        for (int call = 0; call < 52; ++call) {
            LraPropagationEngine::Statistics statistics;
            const auto derived = engine.propagateAll(gs, budget, &statistics);
            CHECK(statistics.rowVisits <= static_cast<std::size_t>(budget.maxIterations));
            CHECK(derived.size() <= static_cast<std::size_t>(budget.maxDerivedBounds));
            for (const auto& bound : derived) {
                const auto found = std::find(variables.begin(), variables.end(), bound.var);
                REQUIRE(found != variables.end());
                const auto row = static_cast<int>(found - variables.begin());
                CHECK(bound.value == DeltaRational((bound.isLower ? -20 : 20) + row));
                REQUIRE(bound.reasons.size() == 1);
                CHECK(bound.reasons.front() == SatLit::positive(2 * row + (bound.isLower ? 1 : 2)));
                reached[2 * row + (bound.isLower ? 0 : 1)] = true;
            }
        }
        CHECK(std::all_of(reached.begin(), reached.end(), [](bool value) { return value; }));
        for (int x : variables) {
            CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
            CHECK_FALSE(gs.varState(x).upper.bound.isFinite());
        }
    }
}

TEST_CASE("LraPropagationEngine: circular scheduling retains no facts across tableaux or rollback") {
    LraPropagationEngine engine;
    GeneralSimplex previous;
    for (int row = 0; row < 5; ++row) previous.addConstraint({}, -row);
    for (int call = 0; call < 7; ++call) engine.propagateAll(previous, {1, 1, 12, 1000});

    GeneralSimplex gs;
    const int x = gs.addVar("fresh-x");
    const int s = gs.addConstraint({{x, 1}}, 0);
    REQUIRE(gs.assertLower(s, mkBound(-3, 101)));
    REQUIRE(gs.assertUpper(s, mkBound(3, 102)));
    auto checkCurrent = [&](bool child) {
        bool lower = false, upper = false;
        for (int call = 0; call < 2; ++call) {
            const auto derived = engine.propagateAll(gs, {1, 1, 12, 1000});
            REQUIRE(derived.size() == 1);
            const auto& bound = derived.front();
            CHECK(bound.var == x);
            CHECK(bound.value == (bound.isLower ? DeltaRational(-3) :
                child ? DeltaRational(mpq_class(1, 2), -1) : DeltaRational(3)));
            REQUIRE(bound.reasons.size() == 1);
            CHECK(bound.reasons.front() == SatLit::positive(bound.isLower ? 101 : child ? 103 : 102));
            (bound.isLower ? lower : upper) = true;
        }
        CHECK(lower);
        CHECK(upper);
    };
    checkCurrent(false);
    gs.push();
    REQUIRE(gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(mpq_class(1, 2), -1)), SatLit::positive(103)), 1));
    checkCurrent(true);
    gs.pop();
    checkCurrent(false);
}

TEST_CASE("LraPropagationEngine: negative target uses the correct extremum of other terms") {
    for (const bool basicLower : {true, false}) {
        CAPTURE(basicLower);
        GeneralSimplex gs;
        const int x = gs.addVar("negative-x"), y = gs.addVar("negative-y");
        const int s = gs.addConstraint({{x, -1}, {y, 1}}, 0);
        REQUIRE(gs.assertLower(y, mkBound(basicLower ? 0 : -10, 1)));
        REQUIRE(gs.assertUpper(y, mkBound(basicLower ? 10 : 0, 2)));
        if (basicLower) REQUIRE(gs.assertLower(s, mkBound(0, 3)));
        else REQUIRE(gs.assertUpper(s, mkBound(0, 3)));
        REQUIRE(gs.check() == GeneralSimplex::Result::Sat);

        LraPropagationEngine engine;
        const auto derived = engine.propagateAll(gs);
        // s = -x+y. s>=0,y<=10 permits x=5,y=10;
        // s<=0,y>=-10 permits x=-5,y=-10.
        const mpq_class witnessX = basicLower ? 5 : -5;
        const mpq_class witnessY = basicLower ? 10 : -10;
        for (const auto& bound : derived) {
            const mpq_class value = bound.var == x ? witnessX :
                bound.var == y ? witnessY : witnessY - witnessX;
            if (bound.isLower) CHECK(DeltaRational(value) >= bound.value);
            else CHECK(DeltaRational(value) <= bound.value);
        }
        CHECK(hasBound(derived, x, !basicLower, basicLower ? 10 : -10));
    }
}

TEST_CASE("LraPropagationEngine: local closure flattens multi-row premises") {
    GeneralSimplex gs;
    const int x = gs.addVar("chain-x"), y = gs.addVar("chain-y"), z = gs.addVar("chain-z");
    const int first = gs.addConstraint({{x, 1}, {y, -1}}, 0);
    const int second = gs.addConstraint({{y, 1}, {z, -1}}, 0);
    REQUIRE(gs.assertLower(first, mkBound(0, 1)));
    REQUIRE(gs.assertLower(second, mkBound(0, 2)));
    REQUIRE(gs.assertLower(z, mkBound(3, 3)));
    // Propagation reasons depend on row identities and active bounds, even
    // before simplex pivots change the basis or repair the primal point.
    LraPropagationEngine engine;
    const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000});
    CHECK(hasBound(derived, y, true, 3));
    CHECK(hasBound(derived, x, true, 3));
    bool checked = false;
    for (const auto& bound : derived) {
        if (bound.var != x || !bound.isLower || bound.value != DeltaRational(3)) continue;
        REQUIRE(bound.reasons.size() == 3);
        for (SatVar reason = 1; reason <= 3; ++reason) {
            CHECK(std::any_of(bound.reasons.begin(), bound.reasons.end(),
                [reason](SatLit literal) { return literal.var == reason && literal.sign; }));
        }
        checked = true;
    }
    CHECK(checked);
    // The local overlay must not assert its conclusions into the source.
    CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(y).lower.bound.isFinite());
}

TEST_CASE("LraPropagationEngine: strict endpoints and empty explanations stay exact") {
    SUBCASE("negative division preserves infinitesimal signs") {
        GeneralSimplex gs;
        const int x = gs.addVar("strict-x"), y = gs.addVar("strict-y");
        const int s = gs.addConstraint({{x, -1}, {y, 1}}, 0);
        REQUIRE(gs.assertLower(y, mkBound(0, 1)));
        REQUIRE(gs.assertUpper(y, BoundInfo(BoundValue(DeltaRational(10, -1)), SatLit::positive(2))));
        REQUIRE(gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(0, 1)), SatLit::positive(3))));
        REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
        LraPropagationEngine engine;
        const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000});
        CHECK(std::any_of(derived.begin(), derived.end(), [x](const auto& bound) {
            return bound.var == x && !bound.isLower && bound.value == DeltaRational(10, -2);
        }));
    }
    SUBCASE("a constant row is an unconditional fact") {
        GeneralSimplex gs;
        const int s = gs.addConstraint({}, -7);
        REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
        LraPropagationEngine engine;
        const auto derived = engine.propagateAll(gs, {8, 32, 0, 1000});
        CHECK(hasBound(derived, s, true, 7));
        CHECK(hasBound(derived, s, false, 7));
        for (const auto& bound : derived) CHECK(bound.reasons.empty());
    }
}

TEST_CASE("LraPropagationEngine: repeated calls after rollback forget child facts") {
    GeneralSimplex gs;
    const int x = gs.addVar("rollback-x"), y = gs.addVar("rollback-y");
    const int s = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    REQUIRE(gs.assertLower(y, mkBound(1, 1)));
    REQUIRE(gs.assertUpper(s, mkBound(5, 2)));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    LraPropagationEngine engine;
    CHECK(hasBound(engine.propagateAll(gs), x, false, 4));
    gs.push();
    REQUIRE(gs.assertLower(y, mkBound(3, 3), 1));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    CHECK(hasBound(engine.propagateAll(gs), x, false, 2));
    gs.pop();
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    const auto restored = engine.propagateAll(gs);
    CHECK(hasBound(restored, x, false, 4));
    CHECK_FALSE(hasBound(restored, x, false, 2));
}

TEST_CASE("LraPropagationEngine: independently replay explanations over signed rows") {
    struct Premise { int var; bool lower; int value; };
    int checkedModels = 0;
    for (int pattern = 0; pattern < 8; ++pattern) {
        for (int shift = -1; shift <= 1; ++shift) {
            CAPTURE(pattern);
            CAPTURE(shift);
            GeneralSimplex gs;
            const int x = gs.addVar("grid-x"), y = gs.addVar("grid-y"), z = gs.addVar("grid-z");
            const int a = (pattern & 1) ? -2 : 2;
            const int b = (pattern & 2) ? -1 : 1;
            const int c = (pattern & 4) ? -2 : 2;
            const int d = (pattern & 1) ? 1 : -1;
            const int first = gs.addConstraint({{x, a}, {y, b}}, shift);
            const int second = gs.addConstraint({{y, c}, {z, d}}, -shift);
            std::vector<Premise> premises;
            auto assertPremise = [&](int var, bool lower, int value) {
                premises.push_back({var, lower, value});
                const auto bound = mkBound(value, static_cast<SatVar>(premises.size()));
                REQUIRE((lower ? gs.assertLower(var, bound) : gs.assertUpper(var, bound)));
            };
            for (const int var : {x, y, z}) {
                assertPremise(var, true, -2);
                assertPremise(var, false, 2);
            }
            if (pattern % 3 != 2) assertPremise(first, true, -1);
            if (pattern % 3 != 0) assertPremise(first, false, 1);
            if (pattern % 3 != 0) assertPremise(second, true, -1);
            if (pattern % 3 != 2) assertPremise(second, false, 1);
            REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
            LraPropagationEngine engine;
            const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000});
            for (const auto& bound : derived) {
                for (const auto literal : bound.reasons) {
                    REQUIRE(literal.sign);
                    REQUIRE(literal.var > 0);
                    REQUIRE(static_cast<size_t>(literal.var) <= premises.size());
                }
                for (int xv = -2; xv <= 2; ++xv) {
                    for (int yv = -2; yv <= 2; ++yv) {
                        for (int zv = -2; zv <= 2; ++zv) {
                            std::vector<int> values(gs.numVars());
                            values[x] = xv; values[y] = yv; values[z] = zv;
                            values[first] = a * xv + b * yv - shift;
                            values[second] = c * yv + d * zv + shift;
                            bool premisesHold = true;
                            for (const auto literal : bound.reasons) {
                                const auto& premise = premises[static_cast<size_t>(literal.var) - 1];
                                const int value = values[premise.var];
                                if (premise.lower ? value < premise.value : value > premise.value) {
                                    premisesHold = false;
                                    break;
                                }
                            }
                            if (!premisesHold) continue;
                            ++checkedModels;
                            const DeltaRational value(values[bound.var]);
                            CHECK((bound.isLower ? value >= bound.value : value <= bound.value));
                        }
                    }
                }
            }
        }
    }
    CHECK(checkedModels > 1000);
}

// ---------------------------------------------------------------------------
// Test cases
// ---------------------------------------------------------------------------

TEST_CASE("LraPropagationEngine: forward lower bound on basic var") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // s = x + 2y - 3   =>   x + 2y = 3 + s
    int s = gs.addConstraint({{x, 1}, {y, 2}}, 3);

    // Assert s >= 0  (x + 2y >= 3)
    gs.assertLower(s, mkBound(0, 1));
    // Assert x >= 2
    gs.assertLower(x, mkBound(2, 2));
    // Assert y >= 1
    gs.assertLower(y, mkBound(1, 3));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // lower(s) = -3 + 1*lower(x) + 2*lower(y) = -3 + 2 + 2 = 1
    CHECK(hasBound(derived, s, true, mpq_class(1)));
}

TEST_CASE("LraPropagationEngine: forward upper bound on basic var") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // s = x + 2y - 3
    int s = gs.addConstraint({{x, 1}, {y, 2}}, 3);

    // Assert s <= 10
    gs.assertUpper(s, mkBound(10, 1));
    // Assert x <= 4
    gs.assertUpper(x, mkBound(4, 2));
    // Assert y <= 3
    gs.assertUpper(y, mkBound(3, 3));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // upper(s) = -3 + 1*upper(x) + 2*upper(y) = -3 + 4 + 6 = 7
    CHECK(hasBound(derived, s, false, mpq_class(7)));
}

TEST_CASE("LraPropagationEngine: backward bound on non-basic var") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // s = x + y - 5   =>   x + y = 5 + s
    int s = gs.addConstraint({{x, 1}, {y, 1}}, 5);

    // Assert s = 0  (x + y = 5)
    gs.assertLower(s, mkBound(0, 1));
    gs.assertUpper(s, mkBound(0, 2));

    // Assert x >= 3
    gs.assertLower(x, mkBound(3, 3));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // upper(y) = (upper(s) + 5 - lower(x)) / 1 = (0 + 5 - 3) = 2
    CHECK(hasBound(derived, y, false, mpq_class(2)));
}

TEST_CASE("LraPropagationEngine: fixed-point chain propagation") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");
    int z = gs.addVar("z");

    // s0 = x + y - 5   =>   x + y = 5
    int s0 = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    // s1 = y + z - 3   =>   y + z = 3
    int s1 = gs.addConstraint({{y, 1}, {z, 1}}, 3);

    // Assert both equalities
    gs.assertLower(s0, mkBound(0, 1));
    gs.assertUpper(s0, mkBound(0, 2));
    gs.assertLower(s1, mkBound(0, 3));
    gs.assertUpper(s1, mkBound(0, 4));

    // Assert x >= 4
    gs.assertLower(x, mkBound(4, 5));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // Step 1: upper(y) = 5 - lower(x) = 5 - 4 = 1
    CHECK(hasBound(derived, y, false, mpq_class(1)));

    // Step 2: lower(z) = 3 - upper(y) = 3 - 1 = 2
    CHECK(hasBound(derived, z, true, mpq_class(2)));
}

TEST_CASE("LraPropagationEngine: no derivation when required bound missing") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // s = x + y - 5
    int s = gs.addConstraint({{x, 1}, {y, 1}}, 5);

    // Only assert x >= 3, no bound on y
    gs.assertLower(x, mkBound(3, 1));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // Cannot derive lower(s) because lower(y) is missing.
    CHECK(countBounds(derived, s, true) == 0);
}

TEST_CASE("LraPropagationEngine: budget limits derivation count") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");
    int z = gs.addVar("z");

    int s0 = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    int s1 = gs.addConstraint({{y, 1}, {z, 1}}, 3);

    gs.assertLower(s0, mkBound(0, 1));
    gs.assertUpper(s0, mkBound(0, 2));
    gs.assertLower(s1, mkBound(0, 3));
    gs.assertUpper(s1, mkBound(0, 4));
    gs.assertLower(x, mkBound(4, 5));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    PropagationBudget tightBudget{1, 100, 12, 20};
    auto derived = engine.propagateAll(gs, tightBudget);

    CHECK(derived.size() <= 1);
}

TEST_CASE("LraPropagationEngine: derived bound not stronger than active") {
    GeneralSimplex gs;
    int x = gs.addVar("x");

    // s = x - 5   =>   x = 5 + s
    int s = gs.addConstraint({{x, 1}}, 5);

    // Assert s >= 0  and  x >= 5
    gs.assertLower(s, mkBound(0, 1));
    gs.assertLower(x, mkBound(5, 2));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // lower(s) = lower(x) - 5 = 5 - 5 = 0, which equals active lower(s).
    // Should NOT be recorded because it's not strictly stronger.
    CHECK(countBounds(derived, s, true) == 0);
}

TEST_CASE("LraPropagationEngine: backward with negative coefficient") {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // s = x - 2y - 1   =>   x - 2y = 1 + s
    int s = gs.addConstraint({{x, 1}, {y, -2}}, 1);

    // Assert s = 0  (x - 2y = 1)
    gs.assertLower(s, mkBound(0, 1));
    gs.assertUpper(s, mkBound(0, 2));

    // Assert x >= 5
    gs.assertLower(x, mkBound(5, 3));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    LraPropagationEngine engine;
    auto derived = engine.propagateAll(gs);

    // From s = x - 2y - 1  =>  y = (x - s - 1) / 2
    // lower(y) = (lower(x) - upper(s) - 1) / 2 = (5 - 0 - 1) / 2 = 2
    CHECK(hasBound(derived, y, true, mpq_class(2)));
}

TEST_CASE("LraPropagationEngine: paired row visits share unchanged input snapshots") {
    GeneralSimplex gs;
    const int x = gs.addVar("paired-x"), y = gs.addVar("paired-y");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    REQUIRE(gs.assertLower(x, mkBound(0, 1)));
    REQUIRE(gs.assertUpper(x, mkBound(1, 2)));
    REQUIRE(gs.assertLower(y, mkBound(0, 3)));
    REQUIRE(gs.assertUpper(y, mkBound(1, 4)));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    LraPropagationEngine engine;
    LraPropagationEngine::Statistics statistics;
    const auto derived = engine.propagateAll(gs, {64, 256, 12, 1000}, &statistics);
    CHECK(hasBound(derived, sum, true, 0));
    CHECK(hasBound(derived, sum, false, 2));
    CHECK(statistics.rowVisits == 2);
    CHECK(statistics.rowSnapshots == 1);
    CHECK(statistics.snapshotHits == 1);
    CHECK(statistics.termPairs == 2);
    CHECK_FALSE(gs.varState(sum).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(sum).upper.bound.isFinite());
}
