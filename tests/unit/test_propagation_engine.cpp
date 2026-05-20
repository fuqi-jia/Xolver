#include <doctest/doctest.h>
#include "theory/arith/lra/LraPropagationEngine.h"
#include "theory/arith/lra/GeneralSimplex.h"

using namespace nlcolver;

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
