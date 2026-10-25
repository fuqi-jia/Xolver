#include <doctest/doctest.h>
#include "search/lra/LraPropagationEngine.h"
#include "search/lra/GeneralSimplex.h"
#include <algorithm>

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
