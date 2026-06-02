// V6 — Sparse-pair Leq/Geq narrowing (extension of V5e from Eq to all
// relations). Shape: a·x^d + b·x^(d-p) rel 0, factored as
//     x^(d-p) · (a·x^p + b)
// with parity case-split on (k = d-p) and second-factor sign.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/icp/IcpEngineQ.h"
#include "theory/arith/icp/ContractorFactoryQ.h"
#include "theory/arith/icp/contractors/RelationContractorQ.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/interval/ReasonedBoxQ.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

namespace {

struct Fixture {
    std::unique_ptr<PolynomialKernel> kernel;
    VarId x;
    PolyId xp;

    Fixture() : kernel(createPolynomialKernel()) {
        x = kernel->getOrCreateVar("x");
        xp = kernel->mkVar(x);
    }

    static SatLit lit(unsigned id) { return SatLit::positive(id); }

    void setBox(ReasonedBoxQ& b, const std::string& var,
                const mpq_class& lo, const mpq_class& hi,
                unsigned reasonId) {
        b.set(var, ReasonedIntervalQ{IntervalQ{lo, hi}, {lit(reasonId)}});
    }

    IcpConstraint cstr(PolyId p, Relation rel, unsigned r) {
        return IcpConstraint{std::nullopt, p, rel, lit(r), TheoryId::NRA};
    }
};

} // namespace

// -- Leq, k even, p even -----------------------------------------------------

TEST_CASE("ICP-Q V6: x⁴ + x² ≤ 0 brackets x to {0} (T < 0 ⇒ g > 0 always)") {
    // x²(x² + 1) ≤ 0. x²+1 > 0 always ⇒ only x = 0 satisfies.
    // k = 2 even, p = 2 even, T = -1 < 0.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 4),
                                 f.kernel->pow(f.xp, 2));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(0));
}

TEST_CASE("ICP-Q V6: x⁴ - x² ≤ 0 brackets x to [-1, 1] (T = 1 > 0)") {
    // x²(x² - 1) ≤ 0 ⇔ x² ≤ 1 OR x = 0. x ∈ [-1, 1].
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId negXSq = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xPow4, negXSq);
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-1));
    CHECK(ri->interval.hi == mpq_class(1));
}

// -- Leq, k odd, p even ------------------------------------------------------

TEST_CASE("ICP-Q V6: x³ + 4x ≤ 0 brackets x ≤ 0 (T < 0 ⇒ g > 0 always)") {
    // x(x²+4) ≤ 0. x²+4 > 0 always ⇒ x ≤ 0.
    // k = 1 odd, p = 2 even, T = -4 < 0.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId fourX = f.kernel->mul(f.kernel->mkConst(mpq_class(4)), f.xp);
    PolyId poly = f.kernel->add(xCube, fourX);
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi == mpq_class(0));  // tight upper bound
    CHECK(ri->interval.lo == mpq_class(-10));
}

TEST_CASE("ICP-Q V6: x³ - 4x ≤ 0 brackets x ≤ 2 (T = 4 > 0)") {
    // x(x²-4) ≤ 0. Sign analysis: x ≤ -2 ⇒ x<0, x²-4>0, product<0 ✓.
    //   -2 ≤ x ≤ 0 ⇒ x≤0, x²-4≤0, product≥0. Not ≤ 0 strictly except x=0.
    //   Hmm actually: x = -1 ⇒ -1 · -3 = 3 > 0. So infeasible.
    // Actually: x(x²-4) ≤ 0 ⇔ x ≤ -2 OR (0 ≤ x ≤ 2). Bracket (-∞, 2].
    // V6 over-approx (k odd, p even, T > 0): bracket (-∞, rt] = (-∞, 2].
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId neg4X = f.kernel->mul(f.kernel->mkConst(mpq_class(-4)), f.xp);
    PolyId poly = f.kernel->add(xCube, neg4X);
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(2));
    CHECK(ri->interval.lo == mpq_class(-10));
}

// -- Leq, k odd, p odd -------------------------------------------------------

TEST_CASE("ICP-Q V6: x² + 4x ≤ 0 — degree 2 handled by V2 first (sanity)") {
    // V2 handles deg-2 (discriminant). Roots: 0, -4. Bracket [-4, 0].
    Fixture f;
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId fourX = f.kernel->mul(f.kernel->mkConst(mpq_class(4)), f.xp);
    PolyId poly = f.kernel->add(xSq, fourX);
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo <= mpq_class(-4));
    CHECK(ri->interval.hi >= mpq_class(0));
    CHECK(ri->interval.lo >= mpq_class(-5));
    CHECK(ri->interval.hi <= mpq_class(1));
}

// -- Geq, k odd, p even (good narrowing case) -------------------------------

TEST_CASE("ICP-Q V6: x³ - 4x ≥ 0 brackets x ≥ -2 (T = 4, k=1 odd, p=2 even)") {
    // x(x²-4) ≥ 0 ⇔ x ∈ [-2, 0] ∪ [2, ∞). Over-approx [-2, ∞).
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId neg4X = f.kernel->mul(f.kernel->mkConst(mpq_class(-4)), f.xp);
    PolyId poly = f.kernel->add(xCube, neg4X);
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-2));
    CHECK(ri->interval.hi == mpq_class(10));
}

TEST_CASE("ICP-Q V6: x³ + 4x ≥ 0 brackets x ≥ 0 (T<0 ⇒ g>0 always)") {
    // x(x²+4) ≥ 0 ⇔ x ≥ 0 (x²+4 > 0 always).
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId fourX = f.kernel->mul(f.kernel->mkConst(mpq_class(4)), f.xp);
    PolyId poly = f.kernel->add(xCube, fourX);
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(10));
}

// -- Geq, k even, p odd ------------------------------------------------------

TEST_CASE("ICP-Q V6: x⁴ - 4x ≥ 0 → V6 declines (k odd p odd union); V5d declines (even-d Geq union)") {
    // x⁴ - 4x = x(x³ - 4). Real roots 0 and ∛4 ≈ 1.587. Feasible set
    // {p ≥ 0} = (-∞, 0] ∪ [∛4, ∞) — a union of two unbounded sets, not
    // a single interval. coeffs [1, 0, 0, -4, 0] ⇒ d=4 (even), p=3 (odd
    // intermediate at coeffs[3]), k=1 (odd common factor).
    //   V6 k-odd p-odd: declines (always union, no narrowing).
    //   V5d a>0 even-d Geq: declines (union of unbounded sets).
    // Result: no narrowing. Soundness preserved (V1 violation check
    // doesn't fire either — interval contains feasible values).
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId neg4X = f.kernel->mul(f.kernel->mkConst(mpq_class(-4)), f.xp);
    PolyId poly = f.kernel->add(xPow4, neg4X);
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-100));
    CHECK(ri->interval.hi == mpq_class(100));
}

// -- Sign-flip (a < 0) -------------------------------------------------------

TEST_CASE("ICP-Q V6: -x³ - 4x ≤ 0 normalizes to a > 0 Geq → bracket x ≥ 0") {
    // After negate: x³ + 4x ≥ 0. Same as the test above ⇒ x ≥ 0.
    Fixture f;
    PolyId xCubeNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                     f.kernel->pow(f.xp, 3));
    PolyId neg4X = f.kernel->mul(f.kernel->mkConst(mpq_class(-4)), f.xp);
    PolyId poly = f.kernel->add(xCubeNeg, neg4X);
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(10));
}

// -- Strict relations (closed over-approx) -----------------------------------

TEST_CASE("ICP-Q V6: x³ + 4x < 0 (Lt) — closed over-approx of (-∞, 0)") {
    // Same as Leq but strict. Closed over-approx: x ≤ 0 (admits boundary).
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId fourX = f.kernel->mul(f.kernel->mkConst(mpq_class(4)), f.xp);
    PolyId poly = f.kernel->add(xCube, fourX);
    auto c = f.cstr(poly, Relation::Lt, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(0));
}

#endif  // XOLVER_HAS_LIBPOLY
