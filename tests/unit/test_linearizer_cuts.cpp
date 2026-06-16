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
#include "theory/arith/linearizer/McCormickGenerator.h"
#include "theory/arith/linearizer/SquareCutGenerator.h"
#include "theory/arith/linearizer/LinearizationTypes.h"

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

static BoundInfo mkBounds(const mpq_class& lo, const mpq_class& hi) {
    BoundInfo b;
    b.lower = lo; b.upper = hi;
    b.hasLower = true; b.hasUpper = true;
    b.lowerReasonComplete = true;
    b.upperReasonComplete = true;
    return b;
}

TEST_CASE("Linearizer: McCormick emits no cuts when bounds incomplete") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    BoundInfo noBounds;  // hasLower/hasUpper default false
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

TEST_CASE("Linearizer: McCormick degenerate bounds (point box)") {
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkBounds(3, 3);  // x = 3 exactly
    auto yb = mkBounds(2, 2);  // y = 2 exactly
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    // Even degenerate boxes should produce cuts (z = 6 is forced).
    CHECK(cuts.size() == 4);
}

TEST_CASE("Linearizer: SquareCut nonneg-only mode produces exactly one") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-10, 10);
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt,
                              /*emitNonneg*/ true, /*emitSecant*/ false, /*emitTangent*/ false);
    CHECK(cuts.size() == 1);
    // The nonneg cut should be s >= 0, which in zero-form is "−s ≤ 0" or "s ≥ 0".
}

TEST_CASE("Linearizer: SquareCut emits secant only with finite bounds") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-5, 5);
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt,
                              /*emitNonneg*/ false, /*emitSecant*/ true, /*emitTangent*/ false);
    CHECK(cuts.size() == 1);  // secant
}

TEST_CASE("Linearizer: SquareCut tangent at sample point") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-10, 10);
    mpq_class sample{3};
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, sample,
                              /*emitNonneg*/ false, /*emitSecant*/ false, /*emitTangent*/ true);
    CHECK(cuts.size() == 1);  // tangent at x=3
}

TEST_CASE("Linearizer: SquareCut tangent without sample uses a fallback or skips") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-10, 10);
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, std::nullopt,
                              /*emitNonneg*/ false, /*emitSecant*/ false, /*emitTangent*/ true);
    // Without explicit sample, generator may either skip or fall back (e.g. use
    // bound midpoint). Either is acceptable; we only assert no crash + bounded count.
    CHECK(cuts.size() <= 1);
}

TEST_CASE("Linearizer: SquareCut all three cuts when fully enabled") {
    SquareCutGenerator gen;
    auto aux = mkAuxSquare("__nl_aux_xsq", VarId{1});
    auto xb = mkBounds(-5, 5);
    mpq_class sample{2};
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, sample,
                              /*emitNonneg*/ true, /*emitSecant*/ true, /*emitTangent*/ true);
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
    auto cuts = gen.generate(aux, "x", xb, SatLit{0, false}, wildSample,
                              /*emitNonneg*/ false, /*emitSecant*/ false, /*emitTangent*/ true);
    // Generator should still produce a tangent at x=1000; semantics-wise it
    // remains a valid lower bound (tangent of convex function is always below).
    CHECK(cuts.size() == 1);
}

// =============================================================================
// MonomialBoundGenerator — Phase 2 cuts on compound monomials.
// =============================================================================
#include "theory/arith/linearizer/MonomialBoundGenerator.h"

static AuxTerm mkAuxHigher(const std::string& name,
                            std::vector<std::pair<VarId,int>> powers) {
    AuxTerm t;
    t.name = name;
    t.vid = NullVar;
    t.poly = NullPoly;
    t.key.kind = NonlinearKind::HigherMixed;
    t.key.powers = std::move(powers);
    return t;
}

static MonomialBoundGenerator::Factor mkF(const std::string& name, int exp,
                                            const mpq_class& lo, const mpq_class& hi,
                                            std::optional<mpq_class> mv = std::nullopt) {
    MonomialBoundGenerator::Factor f;
    f.var = name;
    f.exponent = exp;
    f.bounds = mkBounds(lo, hi);
    f.modelVal = mv;
    return f;
}

TEST_CASE("MonomialBound: <2 factors -> no cuts") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_x3", {{VarId{1}, 3}});
    std::vector<MonomialBoundGenerator::Factor> fs{ mkF("x", 3, 1, 2) };
    MonomialBoundGenerator::Options opt;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    CHECK(cuts.empty());
}

TEST_CASE("MonomialBound: interval-only emits 2 cuts on tight positive box") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_xyz", {{VarId{1},1},{VarId{2},1},{VarId{3},1}});
    std::vector<MonomialBoundGenerator::Factor> fs{
        mkF("x", 1, 1, 2), mkF("y", 1, 1, 2), mkF("z", 1, 1, 2)
    };
    MonomialBoundGenerator::Options opt;
    opt.emitSignOnly = false;  // measure only the interval family
    opt.emitPivotCorner = false;
    opt.emitTangentPlane = false;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    CHECK(cuts.size() == 2);   // lower + upper
}

TEST_CASE("MonomialBound: tangent plane lower bound on all-positive box") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_xy", {{VarId{1},1},{VarId{2},1}});
    std::vector<MonomialBoundGenerator::Factor> fs{
        mkF("x", 1, mpq_class(1), mpq_class(2), mpq_class(1)),
        mkF("y", 1, mpq_class(1), mpq_class(2), mpq_class(1))
    };
    MonomialBoundGenerator::Options opt;
    opt.emitSignOnly = false;  // measure only the tangent-plane family
    opt.emitInterval = false;
    opt.emitPivotCorner = false;
    opt.emitTangentPlane = true;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    CHECK(cuts.size() == 1);
    // Encoded as "-s + y*x + x*y + (xy - x*y - y*x) <= 0", here m=(1,1) so
    // T(x,y) = 1 + 1*(x-1) + 1*(y-1) = x + y - 1; -s + x + y - 1 <= 0  =>  s >= x+y-1
}

TEST_CASE("MonomialBound: pivot-corner emits when even-exponent factor present") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_xy2", {{VarId{1},1},{VarId{2},2}});
    std::vector<MonomialBoundGenerator::Factor> fs{
        mkF("x", 1, mpq_class(1), mpq_class(3)),    // pivot on x is exp=1 -> skipped
        mkF("y", 2, mpq_class(1), mpq_class(2))     // pivot on y is exp=2 -> kicks in
    };
    MonomialBoundGenerator::Options opt;
    opt.emitSignOnly = false;  // measure only the pivot-corner family
    opt.emitInterval = false;
    opt.emitTangentPlane = false;
    opt.emitPivotCorner = true;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    // Only y is a valid pivot. R = c * x has Rlo=1, Rhi=3 (both >=0), branch convex
    // (y in [1,2] all-positive). Family emits exactly 1 cut (the upper).
    CHECK(cuts.size() == 1);
}

TEST_CASE("MonomialBound: mixed-sign odd-exponent skipped on pivot, family stays sound") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_xy3", {{VarId{1},1},{VarId{2},3}});
    std::vector<MonomialBoundGenerator::Factor> fs{
        mkF("x", 1, mpq_class(1), mpq_class(2)),
        mkF("y", 3, mpq_class(-1), mpq_class(1))   // mixed-sign odd: skip pivot, but interval still works
    };
    MonomialBoundGenerator::Options opt;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    // Interval cuts should still emit (2). Pivot family on y skipped (mixed sign).
    // Pivot on x is exp=1, skipped. Tangent requires l_i>=0 for all i — y has
    // l=-1 so this is skipped too.
    CHECK(cuts.size() == 2);
}

TEST_CASE("MonomialBound: missing bounds on any factor -> no cuts") {
    MonomialBoundGenerator gen;
    auto aux = mkAuxHigher("__nl_aux_xy", {{VarId{1},1},{VarId{2},1}});
    MonomialBoundGenerator::Factor fx; fx.var = "x"; fx.exponent = 1; // no bounds
    auto fy = mkF("y", 1, 1, 2);
    std::vector<MonomialBoundGenerator::Factor> fs{ fx, fy };
    MonomialBoundGenerator::Options opt;
    auto cuts = gen.generate(aux, mpq_class(1), fs, SatLit{0, false}, opt);
    CHECK(cuts.empty());
}

// =============================================================================
// BernsteinPowerCutGenerator — Phase 1c convex-hull envelope for x^N on [l,u].
// =============================================================================
#include "theory/arith/linearizer/BernsteinPowerCutGenerator.h"

TEST_CASE("Bernstein: boundary coefficients reproduce l^N and u^N (positive box)") {
    auto b = BernsteinPowerCutGenerator::bernsteinCoeffs(4, mpq_class(1), mpq_class(3));
    REQUIRE(b.size() == 5);
    // b_0 = 1^4 = 1
    CHECK(b.front() == mpq_class(1));
    // b_4 = 3^4 = 81
    CHECK(b.back() == mpq_class(81));
    // Bernstein coefficients of an increasing function on positive box must
    // themselves be non-decreasing (control polygon monotonicity).
    for (size_t i = 1; i < b.size(); ++i) CHECK(b[i] >= b[i - 1]);
}

TEST_CASE("Bernstein: zero-anchored boundary l=0") {
    auto b = BernsteinPowerCutGenerator::bernsteinCoeffs(3, mpq_class(0), mpq_class(2));
    REQUIRE(b.size() == 4);
    CHECK(b.front() == mpq_class(0));  // 0^3 = 0
    CHECK(b.back()  == mpq_class(8));  // 2^3 = 8
}

TEST_CASE("Bernstein: even N, symmetric box around zero, control polygon hits 0 at ends") {
    auto b = BernsteinPowerCutGenerator::bernsteinCoeffs(2, mpq_class(-2), mpq_class(2));
    REQUIRE(b.size() == 3);
    CHECK(b.front() == mpq_class(4));   // (-2)^2 = 4
    CHECK(b.back()  == mpq_class(4));   // 2^2 = 4
    // Bernstein middle coefficient for x^2 on [-l,l] is a known identity:
    //   b_1 = -l*u = 4, b_0 = l^2 = 4, b_2 = u^2 = 4. All 4 here.
    // (Sanity check the formula stays consistent.)
}

TEST_CASE("Bernstein: convex hull min/max bracket actual x^N values") {
    int N = 5;
    mpq_class l(0), u(2);
    auto b = BernsteinPowerCutGenerator::bernsteinCoeffs(N, l, u);
    mpq_class bMin = b[0], bMax = b[0];
    for (auto v : b) { if (v < bMin) bMin = v; if (v > bMax) bMax = v; }
    // Sample x = 1.5  ->  x^5 = 7.59375
    mpq_class xs(3, 2); // 3/2
    mpq_class xN = 1;
    for (int i = 0; i < N; ++i) xN *= xs;
    CHECK(bMin <= xN);
    CHECK(bMax >= xN);
}

static AuxTerm mkAuxPower(const std::string& name, VarId vx, int exp) {
    AuxTerm t;
    t.name = name; t.vid = NullVar; t.poly = NullPoly;
    t.key.kind = NonlinearKind::Power;
    t.key.powers = {{vx, exp}};
    return t;
}

TEST_CASE("Bernstein: generator emits hull cuts on positive box") {
    BernsteinPowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x4", VarId{1}, 4);
    auto xb = mkBounds(1, 3);
    BernsteinPowerCutGenerator::Options opt;
    opt.skipTrivial = false;
    auto cuts = gen.generate(aux, "x", 4, xb, SatLit{0, false}, opt);
    // For x^4 on [1,3]: trivial endpoint min = 1, max = 81.
    // Bernstein control coefficients in degree 4 should give bMin=1, bMax=81.
    // So with skipTrivial=false we still get 2 cuts; with skipTrivial=true
    // (default) we'd get 0 since hull matches trivial.
    CHECK(cuts.size() == 2);
}

TEST_CASE("Bernstein: skipTrivial collapses to 0 cuts when convex hull matches endpoints") {
    BernsteinPowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x4", VarId{1}, 4);
    auto xb = mkBounds(1, 3);
    BernsteinPowerCutGenerator::Options opt;
    opt.skipTrivial = true;
    auto cuts = gen.generate(aux, "x", 4, xb, SatLit{0, false}, opt);
    CHECK(cuts.empty());
}

// ─────────── McCormick partial-bounds extension (XOLVER_NRA_MCCORMICK_PARTIAL) ───────────
// Each envelope cut follows from one sign fact (x−a)(y−b)⪋0 and needs only TWO of the
// four bounds. The gated extension emits the valid subset when the box is partial.
#include <cstdlib>

namespace {
BoundInfo mkLowerOnly(const mpq_class& lo) {
    BoundInfo b; b.lower = lo; b.hasLower = true; b.lowerReasonComplete = true; return b;
}
BoundInfo mkUpperOnly(const mpq_class& hi) {
    BoundInfo b; b.upper = hi; b.hasUpper = true; b.upperReasonComplete = true; return b;
}
// Evaluate a McCormick cut at (xv,yv) with t = xv*yv; true iff its relation holds.
bool mcCutHolds(const LinearCut& c, const std::string& tname,
                const mpq_class& xv, const mpq_class& yv) {
    mpq_class lhs = c.constraint.expr.constant;
    for (const auto& term : c.constraint.expr.terms) {
        mpq_class v = (term.var == "x") ? xv
                    : (term.var == "y") ? yv
                    : (term.var == tname) ? xv * yv : mpq_class(0);
        lhs += term.coeff * v;
    }
    switch (c.constraint.rel) {
        case Relation::Leq: return lhs <= 0;
        case Relation::Lt:  return lhs <  0;
        case Relation::Geq: return lhs >= 0;
        case Relation::Gt:  return lhs >  0;
        case Relation::Eq:  return lhs == 0;
        default:            return lhs != 0;
    }
}
// Grid-validate every partial cut over the box [xlo,xhi]×[ylo,yhi]. The range MUST
// stay within the variables' actual asserted bounds: a partial cut is only valid
// inside the box it was derived from (an upper-corner cut needs x ≤ ux, etc.).
void gridValidate(const std::vector<LinearCut>& cuts, const std::string& tname,
                  long xlo, long xhi, long ylo, long yhi) {
    for (const auto& c : cuts)
        for (long xv = xlo; xv <= xhi; ++xv)
            for (long yv = ylo; yv <= yhi; ++yv)
                CHECK(mcCutHolds(c, tname, mpq_class(xv), mpq_class(yv)));
}
}  // namespace

TEST_CASE("McCormick partial: gated OFF emits nothing on a partial (unpinned) box") {
    unsetenv("XOLVER_NRA_MCCORMICK_PARTIAL");
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkLowerOnly(-3);   // x >= -3, no upper, sign not pinned
    auto yb = mkLowerOnly(-2);   // y >= -2, no upper, sign not pinned
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    CHECK(cuts.empty());         // no sign cut (unpinned), no partial cut (gated off)
}

TEST_CASE("McCormick partial: lower-only box emits exactly cut1 and it is grid-sound") {
    setenv("XOLVER_NRA_MCCORMICK_PARTIAL", "1", 1);
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkLowerOnly(-3);   // x >= -3
    auto yb = mkLowerOnly(-2);   // y >= -2
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    // Only cut1 (needs lx,ly) is emitable; cut2/3/4 need an absent upper bound.
    CHECK(cuts.size() == 1);
    CHECK(cuts[0].debugTag == "mccormick_partial_lower1");
    // x,y unbounded above ⇒ cut1 valid for all x≥-3, y≥-2; sample a finite window.
    gridValidate(cuts, "__nl_aux_xy", -3, 9, -2, 10);
    unsetenv("XOLVER_NRA_MCCORMICK_PARTIAL");
}

TEST_CASE("McCormick partial: x fully bounded, y lower-only emits cut1+cut3, grid-sound") {
    setenv("XOLVER_NRA_MCCORMICK_PARTIAL", "1", 1);
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    auto xb = mkBounds(-3, 5);   // -3 <= x <= 5 (complete)
    auto yb = mkLowerOnly(-2);   // y >= -2 only
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    // cut1 (lx,ly) and cut3 (ux,ly) emitable; cut2/cut4 need uy (absent).
    CHECK(cuts.size() == 2);
    // x is bounded [-3,5] (cut3 needs x ≤ ux=5); y unbounded above.
    gridValidate(cuts, "__nl_aux_xy", -3, 5, -2, 10);
    unsetenv("XOLVER_NRA_MCCORMICK_PARTIAL");
}

TEST_CASE("McCormick partial: incomplete reasons suppress the cut (soundness)") {
    setenv("XOLVER_NRA_MCCORMICK_PARTIAL", "1", 1);
    McCormickGenerator gen;
    auto aux = mkAuxProduct("__nl_aux_xy", VarId{1}, VarId{2});
    BoundInfo xb; xb.lower = -3; xb.hasLower = true;
    xb.lowerReasonComplete = false; xb.lowerIsGlobal = false;   // reason NOT complete
    auto yb = mkLowerOnly(-2);
    auto cuts = gen.generate(aux, "x", "y", xb, yb, SatLit{0, false});
    CHECK(cuts.empty());   // cut1 would need x's lower reason complete — suppressed
    unsetenv("XOLVER_NRA_MCCORMICK_PARTIAL");
}

// ─────────── PowerCutGenerator soundness lock-in (grid-validated) ───────────
// x^N (N>=3): even N is convex everywhere; odd N is convex on x>=0, concave on
// x<=0, and mixed-sign odd intervals must emit NO secant/tangent (wrong-branch
// unsound). Each emitted cut is checked at every half-integer in the box.
#include "theory/arith/linearizer/PowerCutGenerator.h"

namespace {
mpq_class powq(const mpq_class& b, int e) { mpq_class r = 1; for (int i = 0; i < e; ++i) r *= b; return r; }
bool powCutHolds(const LinearCut& c, const std::string& sname, const mpq_class& xv, int N) {
    mpq_class lhs = c.constraint.expr.constant;
    for (const auto& term : c.constraint.expr.terms) {
        mpq_class v = (term.var == "x") ? xv : (term.var == sname) ? powq(xv, N) : mpq_class(0);
        lhs += term.coeff * v;
    }
    switch (c.constraint.rel) {
        case Relation::Leq: return lhs <= 0;
        case Relation::Lt:  return lhs <  0;
        case Relation::Geq: return lhs >= 0;
        case Relation::Gt:  return lhs >  0;
        case Relation::Eq:  return lhs == 0;
        default:            return lhs != 0;
    }
}
// Half-integer grid over [lo,hi] — finer than integers to catch a sign/slope slip.
void powGrid(const std::vector<LinearCut>& cuts, const std::string& sname, int N, long lo, long hi) {
    for (const auto& c : cuts)
        for (long k = 2 * lo; k <= 2 * hi; ++k)
            CHECK(powCutHolds(c, sname, mpq_class(k, 2), N));
}
}  // namespace

TEST_CASE("PowerCut: even x^4 on mixed-sign [-2,3] — nonneg+secant+tangent grid-sound") {
    PowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x4", VarId{1}, 4);
    auto xb = mkBounds(-2, 3);
    auto cuts = gen.generate(aux, "x", 4, xb, SatLit{0, false}, std::nullopt,
                             /*nonneg*/ true, /*secant*/ true, /*tangent*/ true);
    CHECK(cuts.size() == 3);     // even ⇒ convex everywhere ⇒ all three fire
    powGrid(cuts, "__nl_aux_x4", 4, -2, 3);
}

TEST_CASE("PowerCut: odd x^3 on positive [1,3] — convex branch grid-sound") {
    PowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x3", VarId{1}, 3);
    auto xb = mkBounds(1, 3);
    auto cuts = gen.generate(aux, "x", 3, xb, SatLit{0, false}, std::nullopt,
                             true, true, true);
    CHECK(cuts.size() == 3);     // nonneg (x>=0) + convex secant + convex tangent
    powGrid(cuts, "__nl_aux_x3", 3, 1, 3);
}

TEST_CASE("PowerCut: odd x^3 on negative [-3,-1] — concave branch grid-sound") {
    PowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x3", VarId{1}, 3);
    auto xb = mkBounds(-3, -1);
    auto cuts = gen.generate(aux, "x", 3, xb, SatLit{0, false}, std::nullopt,
                             true, true, true);
    CHECK(cuts.size() == 3);     // nonpos (x<=0) + concave secant + concave tangent
    powGrid(cuts, "__nl_aux_x3", 3, -3, -1);
}

TEST_CASE("PowerCut: odd x^3 on mixed-sign [-2,3] emits no secant/tangent (soundness)") {
    PowerCutGenerator gen;
    auto aux = mkAuxPower("__nl_aux_x3", VarId{1}, 3);
    auto xb = mkBounds(-2, 3);
    auto cuts = gen.generate(aux, "x", 3, xb, SatLit{0, false}, std::nullopt,
                             true, true, true);
    // No sign-determinate interval and inflection at 0 ⇒ no secant/tangent.
    for (const auto& c : cuts) {
        CHECK(c.debugTag != "power_secant_convex");
        CHECK(c.debugTag != "power_secant_concave");
        CHECK(c.debugTag != "power_tangent_convex");
        CHECK(c.debugTag != "power_tangent_concave");
    }
}
