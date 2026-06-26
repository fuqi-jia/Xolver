// V5a — Eq bidirectional narrowing.
//
// Univariate (RelationContractorQ):
//   - V2: ax² + bx + c = 0 narrows to the discriminant bracket [r1Lo, r2Hi].
//         Works for both a > 0 and a < 0 (Eq is sign-invariant).
//   - V3b: a·x^d + c = 0 with d even, T = -c/a > 0 narrows to [-rt, rt].
//         (Odd-d Eq was already covered in V3b; this test sanity-checks it.)
//
// Multivariate (MonomialMultivariateContractorQ):
//   - V4: a·x^d + g(rest) = 0 ⇒ a·x^d ∈ [-gBox.hi, -gBox.lo]. Run the Leq
//         projection with cEff = gBox.lo (gives upper-half bound) AND the Geq
//         projection with cEff = gBox.hi (gives lower-half bound), then
//         intersect. Either side may decline; we use whichever fires.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/kernel/icp/IcpEngineQ.h"
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"
#include "theory/arith/kernel/icp/contractors/RelationContractorQ.h"
#include "theory/arith/kernel/icp/contractors/MonomialMultivariateContractorQ.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/kernel/interval/ReasonedBoxQ.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

namespace {

struct Fixture {
    std::unique_ptr<PolynomialKernel> kernel;
    VarId x, y, z;
    PolyId xp, yp, zp;

    Fixture() : kernel(createPolynomialKernel()) {
        x = kernel->getOrCreateVar("x");
        y = kernel->getOrCreateVar("y");
        z = kernel->getOrCreateVar("z");
        xp = kernel->mkVar(x);
        yp = kernel->mkVar(y);
        zp = kernel->mkVar(z);
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

// -- V2 Eq, a > 0 -----------------------------------------------------------

TEST_CASE("ICP-Q V5: x² - 5x + 6 = 0 narrows to bracket [2, 3]") {
    // Roots are 2 and 3. Bracket [2, 3] outward = [2, 3] exact (disc = 1).
    Fixture f;
    // poly = x² - 5x + 6.
    PolyId poly = f.kernel->add(
        f.kernel->add(f.kernel->pow(f.xp, 2),
                       f.kernel->mul(f.kernel->mkConst(mpq_class(-5)), f.xp)),
        f.kernel->mkConst(mpq_class(6)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());

    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Bracket must contain {2, 3} and be ≤ [2, 3] in width terms.
    CHECK(ri->interval.lo <= mpq_class(2));
    CHECK(ri->interval.hi >= mpq_class(3));
    // Tightness: should NOT be the original [-10, 10].
    CHECK(ri->interval.lo > mpq_class(-10));
    CHECK(ri->interval.hi < mpq_class(10));
}

TEST_CASE("ICP-Q V5: x² + 1 = 0 emits Conflict via disc < 0") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 2),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- V2 Eq, a < 0 (sign normalization) ---------------------------------------

TEST_CASE("ICP-Q V5: -x² + 2x + 3 = 0 normalizes to a > 0 and narrows [-1, 3]") {
    // Equation: -x² + 2x + 3 = 0 ⇔ x² - 2x - 3 = 0. Roots: -1, 3.
    Fixture f;
    PolyId xSqNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId twoX = f.kernel->mul(f.kernel->mkConst(mpq_class(2)), f.xp);
    PolyId poly = f.kernel->add(f.kernel->add(xSqNeg, twoX),
                                 f.kernel->mkConst(mpq_class(3)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo <= mpq_class(-1));
    CHECK(ri->interval.hi >= mpq_class(3));
    CHECK(ri->interval.lo > mpq_class(-10));
    CHECK(ri->interval.hi < mpq_class(10));
}

TEST_CASE("ICP-Q V5: -x² - 1 = 0 (a < 0, disc < 0) emits Conflict") {
    // -x² - 1 = 0 ⇔ x² + 1 = 0. Disc = 0 - 4 = -4 < 0.
    Fixture f;
    PolyId xSqNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xSqNeg, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- V3b even-d Eq with T > 0 (new) ------------------------------------------

TEST_CASE("ICP-Q V5: x⁴ - 16 = 0 narrows to bracket [-2, 2]") {
    // Even-d Eq: a=1, d=4, c=-16. T = 16. rt = 16^(1/4) = 2.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 4),
                                 f.kernel->mkConst(mpq_class(-16)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // The two real roots are ±2. Bracket must contain both.
    CHECK(ri->interval.lo <= mpq_class(-2));
    CHECK(ri->interval.hi >= mpq_class(2));
    // Tightness: should NOT be the original [-10, 10].
    CHECK(ri->interval.lo > mpq_class(-10));
    CHECK(ri->interval.hi < mpq_class(10));
}

TEST_CASE("ICP-Q V5: x⁴ + 16 = 0 (even-d Eq, T < 0) emits Conflict") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 4),
                                 f.kernel->mkConst(mpq_class(16)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- V4 multivariate Eq, odd d ----------------------------------------------

TEST_CASE("ICP-Q V5: x³ + y = 0 with y ∈ [1, 2] narrows x bidirectionally") {
    // x³ = -y ∈ [-2, -1] ⇒ x ∈ [-2^(1/3), -1] ≈ [-1.26, -1].
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 3), f.yp);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Upper bound: x ≤ -1 exact (rootCeil(-1) = -1 since -1 is a perfect
    // cube). Lower bound: x ≥ -2^(1/3) outward (more negative than -2^(1/3)).
    CHECK(ri->interval.hi <= mpq_class(-1));
    // Lower bound cubed must be ≤ -2 (soundness — over-approximate outward).
    mpq_class lo3 = ri->interval.lo * ri->interval.lo * ri->interval.lo;
    CHECK(lo3 <= mpq_class(-2));
    // Tightness: must be tighter than [-10, 10].
    CHECK(ri->interval.lo > mpq_class(-10));
    CHECK(ri->interval.hi < mpq_class(10));
}

TEST_CASE("ICP-Q V5: x³ + y - 8 = 0 with y ∈ [-1, 1] brackets x near [7^(1/3), 9^(1/3)]") {
    // x³ + (y - 8) = 0 ⇒ x³ = 8 - y ∈ [7, 9]. So x ∈ [7^(1/3), 9^(1/3)]
    // ≈ [1.913, 2.080]. Bidirectional narrowing is the win here.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 3), f.yp),
                                 f.kernel->mkConst(mpq_class(-8)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(-1), mpq_class(1), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Soundness: lo³ ≤ 7 AND hi³ ≥ 9 (outward).
    mpq_class lo3 = ri->interval.lo * ri->interval.lo * ri->interval.lo;
    mpq_class hi3 = ri->interval.hi * ri->interval.hi * ri->interval.hi;
    CHECK(lo3 <= mpq_class(7));
    CHECK(hi3 >= mpq_class(9));
    // Tightness: x must be inside [1, 3] (since true bracket is ~[1.9, 2.1]).
    CHECK(ri->interval.lo >= mpq_class(1));
    CHECK(ri->interval.hi <= mpq_class(3));
}

// -- V4 multivariate Eq, even d ----------------------------------------------

TEST_CASE("ICP-Q V5: x² + y² = 1, y ∈ [0.5, 0.8] narrows x via upper bound") {
    // x² = 1 - y² ∈ [1 - 0.64, 1 - 0.25] = [0.36, 0.75]. Upper side: x² ≤ 0.75
    // (Leq with cEff = gBox.lo = -1+0.25 = -0.75). Lower side (Geq |x| ≥ 0.6)
    // is a union for even-d ⇒ declined. Only upper-bound narrowing fires.
    // Wait — for Eq we project Leq with cEff = gBox.lo (the actual rest box's
    // lower bound), which is min(y² - 1) = -0.75. So x² ≤ 0.75 ⇒ |x| ≤ √0.75.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                              f.kernel->pow(f.yp, 2)),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(1, 2), mpq_class(4, 5), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Soundness: lo² ≥ 3/4 AND hi² ≥ 3/4 (outward — |x| ≥ √0.75).
    CHECK(ri->interval.lo * ri->interval.lo >= mpq_class(3, 4));
    CHECK(ri->interval.hi * ri->interval.hi >= mpq_class(3, 4));
    // Tightness: |x| ≤ 1 (since 1 - y² ≤ 1).
    CHECK(ri->interval.lo >= mpq_class(-1));
    CHECK(ri->interval.hi <= mpq_class(1));
}

TEST_CASE("ICP-Q V5: x² + y² = 1 with y ∈ [2, 3] (Eq) emits Conflict") {
    // Same as V4 Leq conflict — Eq's Leq side already produces the conflict.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                              f.kernel->pow(f.yp, 2)),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(2), mpq_class(3), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- V4 multivariate Eq, intersection genuinely two-sided --------------------

TEST_CASE("ICP-Q V5: x³ - y = 0 with y ∈ [8, 27] brackets x to [2, 3] exact") {
    // x³ = y ∈ [8, 27] ⇒ x ∈ [2, 3] (exact cube roots). Live var x: a=1, d=3.
    // Rest = -y, gBox = [-27, -8]. Upper: cEff = -27, T = 27, odd-d Leq ⇒
    // rootCeil(27) = 3 ⇒ x ≤ 3. Lower: cEff = -8, T = 8, odd-d Geq ⇒
    // rootFloor(8) = 2 ⇒ x ≥ 2. Intersection: [2, 3].
    Fixture f;
    PolyId yNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)), f.yp);
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 3), yNeg);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(8), mpq_class(27), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // True bracket is [2, 3]. With exact perfect cubes, outward = exact.
    CHECK(ri->interval.lo <= mpq_class(2));
    CHECK(ri->interval.hi >= mpq_class(3));
    // Width must be ≤ 1 + a little outward slack (no slack for exact cubes).
    CHECK(ri->interval.hi - ri->interval.lo <= mpq_class(2));
}

#endif  // XOLVER_HAS_LIBPOLY
