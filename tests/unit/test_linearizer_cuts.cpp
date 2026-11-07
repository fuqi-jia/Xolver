// White-box: McCormickGenerator and SquareCutGenerator semantics.
//
// McCormick relaxation for z = x*y over [xL,xU] × [yL,yU]:
//   z >= xL*y + x*yL - xL*yL   (under-est 1)
//   z >= xU*y + x*yU - xU*yU   (under-est 2)
//   z <= xU*y + x*yL - xU*yL   (over-est  1)
//   z <= xL*y + x*yU - xL*yU   (over-est  2)
//
// Square cuts for s = x^2 over [xL,xU]:
//   s >= 0                            (nonneg)
//   s <= (xL+xU)*x - xL*xU            (secant — over)
//   s >= 2 x0 * x - x0^2              (tangent at sample x0 — under)
//
// Each test checks a structural invariant of the generated cuts. We are not
// re-solving the LP; we are checking that the generator obeys the geometric
// contract above.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "search/linearizer/McCormickGenerator.h"
#include "search/linearizer/SquareCutGenerator.h"
#include "search/linearizer/LinearizationTypes.h"
#include "search/linearizer/IncrementalLinearizer.h"
#include "search/linearizer/BoundStore.h"
#include "search/lra/GeneralSimplex.h"
#include <type_traits>

// Both public internal headers must coexist; separating translation units
// does not make two different xolver::BoundInfo definitions ODR-safe.
static_assert(!std::is_same_v<xolver::LinearizationBounds, xolver::BoundInfo>);

using namespace xolver;

static AuxTerm mkAuxProduct(const std::string& name, VarId vx, VarId vy) {
    AuxTerm t;
    t.name = name;
    t.vid = NullVar;
    t.poly = NullPoly;
    t.key.kind = NonlinearKind::Product;
    t.key.powers = {{vx, 1}, {vy, 1}};
    std::sort(t.key.powers.begin(), t.key.powers.end());
    return t;
}

static AuxTerm mkAuxSquare(const std::string& name, VarId vx) {
    AuxTerm t;
    t.name = name;
    t.vid = NullVar;
    t.poly = NullPoly;
    t.key.kind = NonlinearKind::Square;
    t.key.powers = {{vx, 2}};
    return t;
}

static LinearizationBounds mkBounds(const mpq_class& lo, const mpq_class& hi) {
    LinearizationBounds b;
    b.lower = lo; b.upper = hi;
    b.hasLower = true; b.hasUpper = true;
    b.lowerReasonComplete = true;
    b.upperReasonComplete = true;
    return b;
}

TEST_CASE("Linearizer: McCormick emits no cuts when bounds incomplete") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    LinearizationBounds noBounds;  // hasLower/hasUpper default false
    auto cuts = gen.generate(aux, "x", "y", noBounds, noBounds, SatLit{0, false});
    CHECK(cuts.empty());
}

TEST_CASE("Linearizer: McCormick emits 4 cuts on finite bounds") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkBounds(0, 10);
    auto yb = mkBounds(0, 5);
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    // Standard McCormick relaxation produces 4 cuts (2 under, 2 over).
    CHECK(cuts.size() == 4);
}

TEST_CASE("Linearizer: McCormick faces require only their own justified endpoints") {
    McCormickGenerator gen;
    const auto aux = mkAuxProduct("t", VarId{1}, VarId{2});
    for (bool xLower : {false, true}) for (bool yLower : {false, true}) {
        auto xb = mkBounds(mpq_class(-2, 3), mpq_class(7, 3));
        auto yb = mkBounds(mpq_class(-5, 2), mpq_class(3, 2));
        xb.hasLower = xLower; xb.hasUpper = !xLower;
        yb.hasLower = yLower; yb.hasUpper = !yLower;
        xb.lowerReasons = {SatLit::positive(11)};
        xb.upperReasons = {SatLit::negative(12)};
        yb.lowerReasons = {SatLit::positive(13)};
        yb.upperReasons = {SatLit::negative(14)};
        auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit::positive(10), SortKind::Real);
        REQUIRE(cuts.size() == 1);
        const auto& cut = cuts.front();
        REQUIRE(cut.reasons.size() == 3);
        CHECK(cut.reasons[1] == (xLower ? xb.lowerReasons[0] : xb.upperReasons[0]));
        CHECK(cut.reasons[2] == (yLower ? yb.lowerReasons[0] : yb.upperReasons[0]));
        for (int i = 0; i <= 4; ++i) for (int j = 0; j <= 4; ++j) {
            const mpq_class x = xLower ? mpq_class(xb.lower + mpq_class(i, 3))
                                      : mpq_class(xb.upper - mpq_class(i, 3));
            const mpq_class y = yLower ? mpq_class(yb.lower + mpq_class(j, 3))
                                      : mpq_class(yb.upper - mpq_class(j, 3));
            mpq_class value = cut.constraint.expr.constant;
            for (const auto& term : cut.constraint.expr.terms)
                value += term.coeff * (term.var == "x" ? x : term.var == "y" ? y : mpq_class(x * y));
            CHECK(value <= 0);
        }
        (xLower ? xb.lowerReasonComplete : xb.upperReasonComplete) = false;
        CHECK(gen.generate(aux, "x", "y", xb, yb, SatLit::positive(10)).empty());
        (xLower ? xb.lowerIsGlobal : xb.upperIsGlobal) = true;
        CHECK(gen.generate(aux, "x", "y", xb, yb, SatLit::positive(10)).size() == 1);
    }
}

TEST_CASE("Linearizer: open zero product endpoints preserve strict real signs") {
    McCormickGenerator gen;
    const auto aux = mkAuxProduct("t", VarId{1}, VarId{2});
    for (bool positiveX : {false, true}) for (bool positiveY : {false, true}) {
        auto xb = mkBounds(positiveX ? 0 : -2, positiveX ? 2 : 0);
        auto yb = mkBounds(positiveY ? 0 : -3, positiveY ? 3 : 0);
        (positiveX ? xb.lowerStrict : xb.upperStrict) = true;
        (positiveY ? yb.lowerStrict : yb.upperStrict) = true;
        auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit::positive(10), SortKind::Real);
        REQUIRE(cuts.size() == 4);
        const auto& strict = cuts.back().constraint;
        CHECK(strict.rel == Relation::Lt);
        REQUIRE(strict.expr.terms.size() == 1);
        CHECK(strict.expr.terms[0].coeff == (positiveX == positiveY ? -1 : 1));
        CHECK(strict.expr.constant == 0);
        (positiveY ? yb.lowerStrict : yb.upperStrict) = false;
        cuts = gen.generate(aux, "x", "y", xb, yb, SatLit::positive(10), SortKind::Real);
        CHECK(cuts.size() == 4);
        for (const auto& cut : cuts) CHECK(cut.constraint.rel == Relation::Leq);
    }
}

TEST_CASE("Linearizer: emitted cuts track changed bound explanations and availability") {
#ifdef XOLVER_HAS_LIBPOLY
    auto kernel = createPolynomialKernel();
    REQUIRE(kernel);
    struct Allocator : SatSolver, DynamicAtomRegistrar {
        SatVar next = 0;
        SatVar newVar(VariableRole = VariableRole::Observable) override { return ++next; }
        void addClause(const std::vector<SatLit>&) override {}
        SolveResult solve() override { throw std::logic_error("allocation only"); }
        SolveResult solve(const std::vector<SatLit>&) override { return solve(); }
        bool value(SatVar) const override { throw std::logic_error("allocation only"); }
        void setDeadline(std::chrono::steady_clock::time_point) override {}
        SatLit registerDynamicAtom(ExprId, TheoryId) override {
            return SatLit::positive(newVar());
        }
    } allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator, &allocator);
    const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
    struct Bounds : BoundStore {
        LinearizationBounds x, y;
        std::optional<LinearizationBounds> get(const std::string& name) const override {
            return name == "x" ? x : y;
        }
    } bounds;
    bounds.x = mkBounds(0, 0); bounds.x.hasUpper = false;
    bounds.y = mkBounds(0, 0); bounds.y.hasUpper = false;
    bounds.x.lowerReasons = {SatLit::positive(allocator.newVar())};
    bounds.y.lowerReasons = {SatLit::positive(allocator.newVar())};
    const auto reason = SatLit::positive(allocator.newVar());
    IncrementalLinearizer linearizer(*kernel, &registry);
    const std::vector<LinearizationConstraint> source{
        {kernel->mul(kernel->mkVar(x), kernel->mkVar(y)), Relation::Eq, reason}};
    auto run = [&] { return linearizer.run(source, bounds, TheoryId::NRA, {100, 4}); };
    auto count = [&](const LinearizationResult& result) {
        size_t n = 0;
        for (const auto& pending : result.lemmas) if (pending.cacheKey) {
            ++n;
            linearizer.markEmitted(*pending.cacheKey);
        }
        return n;
    };
    CHECK(count(run()) == 1);
    CHECK(count(run()) == 0);
    bounds.x.lowerReasons = {SatLit::negative(allocator.newVar())};
    CHECK(count(run()) == 1);
    bounds.x.hasLower = false; bounds.x.hasUpper = true;
    bounds.x.upperReasons = {SatLit::positive(allocator.newVar())};
    CHECK(count(run()) == 1);
#endif
}

TEST_CASE("Linearizer: McCormick degenerate bounds (point box)") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkBounds(3, 3);  // x = 3 exactly
    auto yb = mkBounds(2, 2);  // y = 2 exactly
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    // Even degenerate boxes should produce cuts (z = 6 is forced).
    CHECK(cuts.size() == 4);
}

TEST_CASE("Linearizer: SquareCut without bounds or a sample emits nonnegativity") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    LinearizationBounds xb;
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt);
    CHECK(cuts.size() == 1);
    // The nonneg cut should be s >= 0, which in zero-form is "−s ≤ 0" or "s ≥ 0".
}

TEST_CASE("Linearizer: SquareCut emits secant only with finite bounds") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-5, 5);
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt);
    CHECK(cuts.size() == 3);
    xb.upperReasonComplete = false;
    cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt);
    CHECK(cuts.size() == 1);  // no secant without complete bound evidence
}

TEST_CASE("Linearizer: SquareCut tangent at sample point") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-10, 10);
    mpq_class sample{3};
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, sample);
    REQUIRE(cuts.size() == 3);
    CHECK(cuts.back().constraint.debugTag == "square_tangent");
    CHECK(cuts.back().constraint.expr.constant == mpq_class(-9));
}

TEST_CASE("Linearizer: SquareCut tangent without sample uses the bound midpoint") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-10, 10);
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt);
    REQUIRE(cuts.size() == 3);
    CHECK(cuts.back().constraint.expr.constant == 0);
}

TEST_CASE("Linearizer: SquareCut emits every justified cut") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-5, 5);
    mpq_class sample{2};
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, sample);
    CHECK(cuts.size() == 3);
}

TEST_CASE("Linearizer: McCormick over negative-spanning x bounds") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkBounds(-3, 7);  // crosses zero
    auto yb = mkBounds(2, 4);
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    CHECK(cuts.size() == 4);
}

TEST_CASE("Linearizer: SquareCut with sample outside bounds — graceful") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(0, 10);
    mpq_class wildSample{1000};  // outside [0, 10]
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, wildSample);
    // Generator should still produce a tangent at x=1000; semantics-wise it
    // remains a valid lower bound (tangent of convex function is always below).
    REQUIRE(cuts.size() == 3);
    CHECK(cuts.back().constraint.expr.constant == mpq_class(-1000000));
}

// =============================================================================

TEST_CASE("Linearizer: automatic square cuts hold exactly throughout their justified interval") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("s", VarId{1});
    auto bounds = mkBounds(-2, 3);
    bounds.lowerReasons = {SatLit{11, true}};
    bounds.upperReasons = {SatLit{12, true}};
    for (auto sort : {SortKind::Int, SortKind::Real}) {
        for (long sample : {-5L, 0L, 10L}) {
            auto cuts = gen.generate(aux, "x", bounds, SatLit{10, true}, mpq_class(sample), sort);
            REQUIRE(cuts.size() == 3);
            for (const auto& cut : cuts) {
                CHECK(cut.constraint.sort == sort);
                CHECK(cut.constraint.rel == Relation::Leq);
                if (cut.constraint.debugTag == "square_secant") {
                    REQUIRE(cut.reasons.size() == 3);
                    CHECK(cut.reasons[1] == bounds.lowerReasons[0]);
                    CHECK(cut.reasons[2] == bounds.upperReasons[0]);
                }
                for (long numerator = -8; numerator <= 12; ++numerator) {
                    mpq_class x(numerator, 4);
                    x.canonicalize();
                    mpq_class value = cut.constraint.expr.constant;
                    for (const auto& term : cut.constraint.expr.terms) {
                        REQUIRE((term.var == "x" || term.var == "s"));
                        mpq_class point = term.var == "x" ? x : mpq_class(x * x);
                        value += term.coeff * point;
                    }
                    CAPTURE(sample);
                    CAPTURE(numerator);
                    CAPTURE(cut.constraint.debugTag);
                    CHECK(value <= 0);
                }
            }
        }
    }
}
