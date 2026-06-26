// V5c — BilinearContractorQ tests.
//
// Shape: B(rest) · liveVar + C(rest)  rel  0  (no live^2 term).
// When B is sign-pinned (Bl > 0 or Bh < 0), solve via interval division:
// x ≤ D/B (Leq, B > 0) etc. When 0 ∈ B's range, decline.
//
// Closes the "Mixed terms (x·y)" coverage gap.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/kernel/icp/IcpEngineQ.h"
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"
#include "theory/arith/kernel/icp/contractors/BilinearContractorQ.h"
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

// -- Shape detection ---------------------------------------------------------

TEST_CASE("ICP-Q V5c: x·y - 1 detects on x (live^1 mixed, no live^2)") {
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    BilinearContractorQ cx(c, *f.kernel, "x");
    CHECK(cx.isUsable());
}

TEST_CASE("ICP-Q V5c: x²+y declines (has live^2)") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 2), f.yp);
    auto c = f.cstr(poly, Relation::Leq, 200);

    BilinearContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

TEST_CASE("ICP-Q V5c: y² (no live x) declines") {
    Fixture f;
    PolyId poly = f.kernel->pow(f.yp, 2);
    auto c = f.cstr(poly, Relation::Leq, 200);

    BilinearContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

// -- Narrowing — Eq via interval division -----------------------------------

TEST_CASE("ICP-Q V5c: x·y - 1 = 0 with y ∈ [1, 2] narrows x to [1/2, 1]") {
    // x·y = 1, y ∈ [1, 2] ⇒ x ∈ [1/2, 1] (hyperbolic feasible region).
    // B = y ∈ [1, 2] (sign-pinned positive). C = -1. D = -C = 1.
    // 1/B ∈ [1/2, 1]. r = D · 1/B = [1/2, 1].
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Soundness: bracket contains [1/2, 1].
    CHECK(ri->interval.lo <= mpq_class(1, 2));
    CHECK(ri->interval.hi >= mpq_class(1));
    // Tightness: exact (no over-approx needed for rational division).
    CHECK(ri->interval.lo == mpq_class(1, 2));
    CHECK(ri->interval.hi == mpq_class(1));
}

TEST_CASE("ICP-Q V5c: x·y - 1 = 0 with y ∈ [-2, -1] narrows x to [-1, -1/2]") {
    // x·y = 1, y < 0 ⇒ x < 0. x ∈ [-1, -1/2] (negative hyperbolic branch).
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(-2), mpq_class(-1), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo <= mpq_class(-1));
    CHECK(ri->interval.hi >= mpq_class(-1, 2));
    CHECK(ri->interval.lo == mpq_class(-1));
    CHECK(ri->interval.hi == mpq_class(-1, 2));
}

// -- Narrowing — Leq with B sign-pinned -------------------------------------

TEST_CASE("ICP-Q V5c: x·y + 3 ≤ 0 with y ∈ [2, 4] narrows x ≤ -3/4") {
    // Constraint y·x + 3 ≤ 0 asks "∃ y in box such that y·x ≤ -3". For
    // x ≤ 0, y·x is most-negative when y is largest, so the tight
    // bound is 4·x ≤ -3 ⇔ x ≤ -3/4. (Note: x ≤ -3/2 would be the
    // ∀-quantified bound — much tighter but unsound for ICP, which
    // narrows to feasibility-over-the-box not feasibility-everywhere.)
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(3)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(2), mpq_class(4), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(-3, 4));
    CHECK(ri->interval.lo == mpq_class(-10));  // lower untouched
}

TEST_CASE("ICP-Q V5c: x·y + 3 ≤ 0 with y ∈ [-4, -2] narrows x ≥ 3/4") {
    // y < 0, so x ≥ -3/y. min(-3/y) over y ∈ [-4, -2]: y < 0, -3/y > 0,
    // min when -3/y smallest ⇒ y most negative ⇒ -3/(-4) = 3/4.
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(3)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(-4), mpq_class(-2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(3, 4));
    CHECK(ri->interval.hi == mpq_class(10));  // upper untouched
}

// -- Decline when B straddles 0 ----------------------------------------------

TEST_CASE("ICP-Q V5c: x·y - 1 = 0 with y ∈ [-1, 1] (B straddles 0) NoChange") {
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
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
    CHECK(ri->interval.lo == mpq_class(-10));
    CHECK(ri->interval.hi == mpq_class(10));
}

// -- Multiple rest vars in B -------------------------------------------------

TEST_CASE("ICP-Q V5c: x·y·z = 6 with y, z ∈ [1, 2] narrows x") {
    // B = y·z ∈ [1, 4] (sign-pinned positive). x·(y·z) = 6 ⇒ x = 6/(y·z).
    // x ∈ [6/4, 6/1] = [3/2, 6].
    Fixture f;
    PolyId xyz = f.kernel->mul(f.kernel->mul(f.xp, f.yp), f.zp);
    PolyId poly = f.kernel->add(xyz, f.kernel->mkConst(mpq_class(-6)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);
    f.setBox(box, "z", mpq_class(1), mpq_class(2), 102);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo <= mpq_class(3, 2));
    CHECK(ri->interval.hi >= mpq_class(6));
    // Should be ≤ [3/2, 6] in width terms (within the over-approx slack).
    CHECK(ri->interval.lo >= mpq_class(1));
    CHECK(ri->interval.hi <= mpq_class(7));
}

// -- Conflict via narrowing -------------------------------------------------

TEST_CASE("ICP-Q V5c: x·y - 1 = 0 with y ∈ [1, 2] and x ∈ [2, 3] emits Conflict") {
    // x must be in [1/2, 1] but starts in [2, 3] ⇒ intersection empty.
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(2), mpq_class(3), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- Pure live^1 with constant (degenerate "univariate" case multivariate-shaped)

TEST_CASE("ICP-Q V5c: 2x + y = 0 with y ∈ [4, 6] narrows x to [-3, -2]") {
    // 2·x + y = 0 ⇒ x = -y/2. y ∈ [4, 6] ⇒ x ∈ [-3, -2].
    // B = 2 (constant from pure live term). C = y ∈ [4, 6]. D = -C ∈ [-6, -4].
    // 1/B = [1/2, 1/2]. r = D · 1/B = [-3, -2].
    Fixture f;
    PolyId twoX = f.kernel->mul(f.kernel->mkConst(mpq_class(2)), f.xp);
    PolyId poly = f.kernel->add(twoX, f.yp);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(4), mpq_class(6), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo <= mpq_class(-3));
    CHECK(ri->interval.hi >= mpq_class(-2));
    CHECK(ri->interval.lo == mpq_class(-3));
    CHECK(ri->interval.hi == mpq_class(-2));
}

// -- Factory routing ---------------------------------------------------------

TEST_CASE("ICP-Q V5c: factory routes x·y - 1 = 0 to V5c per live var (2 contractors)") {
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(xy, f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    // For x: V4 declines (x·y mixed), V5b declines (no x²), V5c accepts.
    // For y: symmetric. → 2 contractors.
    CHECK(built.contractors.size() == 2);
}

#endif  // XOLVER_HAS_LIBPOLY
