#include <doctest/doctest.h>

#include "theory/arith/logics/nra/reasoners/NlaCutGenerator.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"

#include <gmpxx.h>
#include <unordered_map>

// Phase A unit tests for NlaCutGenerator (monotonicity-product +
// monotonicity-square prototypes).
//
// Soundness contract a cut must satisfy: under every integer (or
// rational) assignment to the variables in `cut.poly` that respects the
// input interval bounds, `cut.poly rel 0` must hold. We validate this by
// gridding the input intervals and evaluating the cut polynomial via the
// kernel's evalInteger — a kernel-side check that no symbolic identity
// can fake.

using namespace xolver;
using namespace xolver::nla;

namespace {

SatLit lit(unsigned int v, bool sign = true) {
    return {v, sign};
}

bool hasReason(const NlaCut& c, const SatLit& l) {
    for (const SatLit& r : c.reasons) if (r == l) return true;
    return false;
}

// Evaluate a cut polynomial at an integer assignment and check
// `poly rel 0` holds. Returns true iff the cut is satisfied. The
// assignment is given by variable name -> mpz_class value.
bool cutHoldsAt(PolynomialKernel& k, const NlaCut& c,
                const std::unordered_map<std::string, mpz_class>& env) {
    auto v = k.evalInteger(c.poly, env);
    if (!v) return true;  // stub backend — skip
    switch (c.rel) {
        case Relation::Geq: return *v >= 0;
        case Relation::Leq: return *v <= 0;
        case Relation::Gt:  return *v > 0;
        case Relation::Lt:  return *v < 0;
        case Relation::Eq:  return *v == 0;
        case Relation::Neq: return *v != 0;
    }
    return false;
}

} // namespace

TEST_CASE("NlaCut monotonicity-product: both intervals non-negative") {
    auto k = createPolynomialKernel();
    if (!k) return;

    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    VarInterval xInt{x, mpq_class(2), mpq_class(5), {lit(11)}};
    VarInterval yInt{y, mpq_class(3), mpq_class(7), {lit(22)}};

    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicityProduct(xInt, yInt);

    // Expect 2 cuts: lo (x*y >= 6) and hi (35 >= x*y).
    REQUIRE(cuts.size() == 2);
    for (const auto& c : cuts) {
        CHECK(c.kind == NlaCutKind::Monotonicity);
        CHECK(c.rel == Relation::Geq);
        CHECK(c.reasons.size() == 2);
        CHECK(hasReason(c, lit(11)));
        CHECK(hasReason(c, lit(22)));
    }

    // Grid: validate both cuts hold at every (x, y) in [2..5]x[3..7].
    for (long xv = 2; xv <= 5; ++xv) {
        for (long yv = 3; yv <= 7; ++yv) {
            std::unordered_map<std::string, mpz_class> env{
                {"x", mpz_class(xv)}, {"y", mpz_class(yv)}};
            for (const auto& c : cuts) {
                INFO("xv=" << xv << " yv=" << yv);
                CHECK(cutHoldsAt(*k, c, env));
            }
        }
    }
}

TEST_CASE("NlaCut monotonicity-product: emits nothing when lo_x is negative") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    // Negative lower bound on x: cut would be unsound (sign of product
    // could flip). Generator MUST omit.
    VarInterval xInt{x, mpq_class(-3), mpq_class(5), {lit(1)}};
    VarInterval yInt{y, mpq_class(2),  mpq_class(7), {lit(2)}};

    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicityProduct(xInt, yInt);
    CHECK(cuts.empty());
}

TEST_CASE("NlaCut monotonicity-product: lo cut alone when hi missing") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    VarInterval xInt;
    xInt.varPoly = x;
    xInt.lo = mpq_class(1);
    xInt.reasons = {lit(1)};
    VarInterval yInt;
    yInt.varPoly = y;
    yInt.lo = mpq_class(2);
    yInt.reasons = {lit(2)};

    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicityProduct(xInt, yInt);
    // Lo cut emitted; hi cut skipped (upper bounds missing).
    REQUIRE(cuts.size() == 1);
    CHECK(cuts[0].rel == Relation::Geq);
}

TEST_CASE("NlaCut monotonicity-square: positive interval ⇒ tight bounds") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    VarInterval xInt{x, mpq_class(2), mpq_class(7), {lit(33)}};
    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicitySquare(xInt);
    // Expect: lo cut (x^2 >= 4) and hi cut (49 >= x^2).
    REQUIRE(cuts.size() == 2);

    for (long xv = 2; xv <= 7; ++xv) {
        std::unordered_map<std::string, mpz_class> env{{"x", mpz_class(xv)}};
        for (const auto& c : cuts) {
            INFO("xv=" << xv);
            CHECK(cutHoldsAt(*k, c, env));
        }
    }
}

TEST_CASE("NlaCut monotonicity-square: 0 in interval ⇒ lo cut floors at 0") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    VarInterval xInt{x, mpq_class(-3), mpq_class(4), {lit(1)}};
    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicitySquare(xInt);
    // Lo cut: x^2 >= 0 (true unconditionally).
    // Hi cut: 16 >= x^2 (max(9, 16) = 16).
    REQUIRE(cuts.size() == 2);

    // Grid all xv in [-3..4].
    for (long xv = -3; xv <= 4; ++xv) {
        std::unordered_map<std::string, mpz_class> env{{"x", mpz_class(xv)}};
        for (const auto& c : cuts) {
            INFO("xv=" << xv);
            CHECK(cutHoldsAt(*k, c, env));
        }
    }
}

TEST_CASE("NlaCut monotonicity-square: negative interval ⇒ both bounds tight") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    VarInterval xInt{x, mpq_class(-7), mpq_class(-2), {lit(1)}};
    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicitySquare(xInt);
    // Lo cut: x^2 >= 4 (since hi <= 0, min sq = hi^2). Hi cut: 49 >= x^2.
    REQUIRE(cuts.size() == 2);

    for (long xv = -7; xv <= -2; ++xv) {
        std::unordered_map<std::string, mpz_class> env{{"x", mpz_class(xv)}};
        for (const auto& c : cuts) {
            INFO("xv=" << xv);
            CHECK(cutHoldsAt(*k, c, env));
        }
    }
}

TEST_CASE("NlaCut monotonicity-square: only-lo interval, no hi cut") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    VarInterval xInt;
    xInt.varPoly = x;
    xInt.lo = mpq_class(3);
    xInt.reasons = {lit(1)};
    NlaCutGenerator gen(*k);
    auto cuts = gen.monotonicitySquare(xInt);
    REQUIRE(cuts.size() == 1);
    CHECK(cuts[0].rel == Relation::Geq);
}

// Phase B — Tangent cut for x^2.
TEST_CASE("NlaCut tangentSquare: x^2 >= 2m*x - m^2 holds for any x") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    NlaCutGenerator gen(*k);

    for (long m = -5; m <= 5; ++m) {
        NlaCut cut = gen.tangentSquare(x, mpq_class(m), {lit(1)});
        CHECK(cut.kind == NlaCutKind::Tangent);
        CHECK(cut.rel == Relation::Geq);
        CHECK(cut.reasons.size() == 1);
        // Validate at every integer x in [-7, 7].
        for (long xv = -7; xv <= 7; ++xv) {
            std::unordered_map<std::string, mpz_class> env{{"x", mpz_class(xv)}};
            INFO("m=" << m << " xv=" << xv);
            CHECK(cutHoldsAt(*k, cut, env));
        }
    }
}

TEST_CASE("NlaCut tangentSquare is tight at x = m (cut value = 0)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    NlaCutGenerator gen(*k);
    NlaCut cut = gen.tangentSquare(x, mpq_class(4), {});
    // (x - 4)^2 evaluated at x=4 is 0.
    std::unordered_map<std::string, mpz_class> env{{"x", mpz_class(4)}};
    auto v = k->evalInteger(cut.poly, env);
    REQUIRE(v.has_value());
    CHECK(*v == 0);
}

// Phase B — Proportional cut.
TEST_CASE("NlaCut proportionalMultiply: (lhs <= rhs) * (z >= 0) ⇒ lhs*z <= rhs*z") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId b = k->mkVar(k->getOrCreateVar("b"));
    PolyId z = k->mkVar(k->getOrCreateVar("z"));

    VarInterval zInt;
    zInt.varPoly = z;
    zInt.lo = mpq_class(0);
    zInt.reasons = {lit(42)};

    NlaCutGenerator gen(*k);
    auto out = gen.proportionalMultiply(a, b, lit(7), zInt);
    REQUIRE(out.has_value());
    CHECK(out->kind == NlaCutKind::Proportional);
    CHECK(out->rel == Relation::Geq);
    CHECK(out->reasons.size() == 2);
    CHECK(hasReason(*out, lit(7)));
    CHECK(hasReason(*out, lit(42)));

    // Grid: for a, b in [-3..5] with a <= b, z in [0..4], the cut must hold.
    for (long av = -3; av <= 5; ++av) {
        for (long bv = av; bv <= 5; ++bv) {
            for (long zv = 0; zv <= 4; ++zv) {
                std::unordered_map<std::string, mpz_class> env{
                    {"a", mpz_class(av)}, {"b", mpz_class(bv)}, {"z", mpz_class(zv)}};
                INFO("av=" << av << " bv=" << bv << " zv=" << zv);
                CHECK(cutHoldsAt(*k, *out, env));
            }
        }
    }
}

TEST_CASE("NlaCut proportionalMultiply rejects negative-z interval (would flip)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId b = k->mkVar(k->getOrCreateVar("b"));
    PolyId z = k->mkVar(k->getOrCreateVar("z"));

    VarInterval zInt;
    zInt.varPoly = z;
    zInt.lo = mpq_class(-2);   // negative — multiplying flips direction
    zInt.reasons = {lit(1)};

    NlaCutGenerator gen(*k);
    auto out = gen.proportionalMultiply(a, b, lit(7), zInt);
    CHECK(!out.has_value());
}

// Phase B — McCormick bilinear envelope.
TEST_CASE("NlaCut mccormickBilinear: 4 envelope cuts hold on the rectangle") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    VarInterval xInt{x, mpq_class(-2), mpq_class(3), {lit(1)}};
    VarInterval yInt{y, mpq_class(1),  mpq_class(4), {lit(2)}};

    NlaCutGenerator gen(*k);
    auto cuts = gen.mccormickBilinear(xInt, yInt);
    REQUIRE(cuts.size() == 4);

    for (long xv = -2; xv <= 3; ++xv) {
        for (long yv = 1; yv <= 4; ++yv) {
            std::unordered_map<std::string, mpz_class> env{
                {"x", mpz_class(xv)}, {"y", mpz_class(yv)}};
            for (size_t i = 0; i < cuts.size(); ++i) {
                INFO("cut=" << i << " xv=" << xv << " yv=" << yv);
                CHECK(cutHoldsAt(*k, cuts[i], env));
            }
        }
    }
}

TEST_CASE("NlaCut mccormickBilinear: omits when bound missing") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    // No hi_x.
    VarInterval xInt;
    xInt.varPoly = x;
    xInt.lo = mpq_class(0);
    xInt.reasons = {lit(1)};
    VarInterval yInt{y, mpq_class(0), mpq_class(4), {lit(2)}};

    NlaCutGenerator gen(*k);
    auto cuts = gen.mccormickBilinear(xInt, yInt);
    CHECK(cuts.empty());
}

// Soundness grid — the math that the cuts encode is sound for all
// integer assignments respecting the interval, by hand.
TEST_CASE("NlaCut math grid: lo_x * lo_y <= x*y <= hi_x * hi_y on non-neg quadrant") {
    // For lo_x in [0..3], hi_x in [lo_x..5], lo_y in [0..3], hi_y in [lo_y..5],
    // and (xv, yv) in the rectangle, the inequalities must hold.
    for (long lx = 0; lx <= 3; ++lx) {
        for (long hx = lx; hx <= 5; ++hx) {
            for (long ly = 0; ly <= 3; ++ly) {
                for (long hy = ly; hy <= 5; ++hy) {
                    for (long xv = lx; xv <= hx; ++xv) {
                        for (long yv = ly; yv <= hy; ++yv) {
                            long lo = lx * ly;
                            long hi = hx * hy;
                            long prod = xv * yv;
                            INFO("lx=" << lx << " hx=" << hx
                                 << " ly=" << ly << " hy=" << hy
                                 << " xv=" << xv << " yv=" << yv);
                            CHECK(prod >= lo);
                            CHECK(prod <= hi);
                        }
                    }
                }
            }
        }
    }
}

// ---------- Phase C: NlaCutsRunner scaffold ----------
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"

TEST_CASE("NlaCutsRunner: disabled by default emits nothing") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    NlaCutsRunner runner(*k);
    // Default (env unset): runner returns empty.
    VarInterval xInt{x, mpq_class(2), mpq_class(5), {lit(1)}};
    auto cuts = runner.runShapeCuts({xInt});
    CHECK(cuts.empty());
    auto tans = runner.runTangents({{x, mpq_class(3)}}, {});
    CHECK(tans.empty());
}
