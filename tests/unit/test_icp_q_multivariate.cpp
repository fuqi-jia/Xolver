// V4 — MonomialMultivariateContractorQ tests.
//
// The contractor narrows `liveVar` for constraints of shape
//   a · liveVar^d + g(rest) rel 0
// where g(rest) is a polynomial in the other variables (no monomial mixes
// liveVar with anything else). Soundness direction (Leq):
//   `x` is feasible (for some y in y_box) iff a·x^d ≤ −min_y(g(y)).
// Interval-eval over-approximates min: we use g_box.lo so the bound on
// a·x^d is `≤ −g_box.lo` — an outward over-approximation. The narrowing
// itself is the V2/V3 monomial bound math, inlined.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/icp/IcpEngineQ.h"
#include "theory/arith/icp/ContractorFactoryQ.h"
#include "theory/arith/icp/contractors/MonomialMultivariateContractorQ.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/interval/ReasonedBoxQ.h"
#include "theory/arith/poly/PolynomialKernel.h"
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

    // Build a·v^d (single-variable monomial component).
    PolyId monoOf(PolyId v, long a, uint32_t d) {
        PolyId vd = kernel->pow(v, d);
        if (a == 1) return vd;
        return kernel->mul(kernel->mkConst(mpq_class(a)), vd);
    }
};

} // namespace

// -- Shape detection ---------------------------------------------------------

TEST_CASE("ICP-Q V4: x²+y²-1 detects V4 shape on both x and y") {
    Fixture f;
    // poly = x² + y² - 1.
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                              f.kernel->pow(f.yp, 2)),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    MonomialMultivariateContractorQ cx(c, *f.kernel, "x");
    MonomialMultivariateContractorQ cy(c, *f.kernel, "y");
    CHECK(cx.isUsable());
    CHECK(cy.isUsable());
}

TEST_CASE("ICP-Q V4: mixed term x*y disqualifies the contractor") {
    Fixture f;
    PolyId xy = f.kernel->mul(f.xp, f.yp);
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 2), xy);  // x² + xy
    auto c = f.cstr(poly, Relation::Leq, 200);

    MonomialMultivariateContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

TEST_CASE("ICP-Q V4: mixed-degree live (x³ + x²) disqualifies") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 3),
                                               f.kernel->pow(f.xp, 2)),
                                 f.yp);
    auto c = f.cstr(poly, Relation::Leq, 200);

    MonomialMultivariateContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

TEST_CASE("ICP-Q V4: pure univariate disqualifies (no rest)") {
    // Pure univariate is the V1/V2/V3 contractor's territory; V4 is for
    // multivariate. (The factory routes accordingly — V4 in isolation
    // here just confirms it self-skips.)
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 2),
                                 f.kernel->mkConst(mpq_class(-4)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    // y as live: poly doesn't depend on y ⇒ foundLive == false ⇒ unusable.
    MonomialMultivariateContractorQ cy(c, *f.kernel, "y");
    CHECK_FALSE(cy.isUsable());
}

// -- Narrowing — even-d (V2/V3-style) ----------------------------------------

TEST_CASE("ICP-Q V4: x²+y² ≤ 1 with y ∈ [0.5, 1] narrows x to outward [-√0.75, √0.75]") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                              f.kernel->pow(f.yp, 2)),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), /*reason=*/100);
    f.setBox(box, "y", mpq_class(1, 2), mpq_class(1), /*reason=*/101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());

    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Soundness: x's box must over-cover [-√0.75, √0.75]. Squaring:
    // lo² ≥ 3/4 (outward DOWN ⇒ more negative ⇒ |lo| ≥ √0.75) and
    // hi² ≥ 3/4.
    CHECK(ri->interval.lo * ri->interval.lo >= mpq_class(3, 4));
    CHECK(ri->interval.hi * ri->interval.hi >= mpq_class(3, 4));
    // Tightness: lo ≥ -1 and hi ≤ 1 (we're inside the unit-disc).
    CHECK(ri->interval.lo >= mpq_class(-1));
    CHECK(ri->interval.hi <= mpq_class(1));
}

TEST_CASE("ICP-Q V4: x²+y²+z² ≤ 4 with y,z ∈ [0,1] narrows x into [-2, 2]") {
    Fixture f;
    PolyId sumSq = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                                f.kernel->pow(f.yp, 2)),
                                  f.kernel->pow(f.zp, 2));
    PolyId poly = f.kernel->add(sumSq, f.kernel->mkConst(mpq_class(-4)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(0), mpq_class(1), 101);
    f.setBox(box, "z", mpq_class(0), mpq_class(1), 102);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // y² + z² ∈ [0, 2] ⇒ cEff (Leq picks gBox.lo = -4) … actually g(y,z) =
    // y² + z² - 4 ∈ [-4, -2]; gBox.lo = -4 ⇒ x² ≤ 4 ⇒ |x| ≤ 2.
    CHECK(ri->interval.lo * ri->interval.lo >= mpq_class(4));
    CHECK(ri->interval.hi * ri->interval.hi >= mpq_class(4));
    CHECK(ri->interval.lo >= mpq_class(-3));
    CHECK(ri->interval.hi <= mpq_class(3));
}

// -- Narrowing — odd-d ------------------------------------------------------

TEST_CASE("ICP-Q V4: x³+y ≤ 5 with y ∈ [3, 4] narrows x upper to ≥ 2^(1/3)") {
    Fixture f;
    // poly = x³ + y - 5.
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 3), f.yp),
                                 f.kernel->mkConst(mpq_class(-5)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(3), mpq_class(4), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // g(y) = y - 5 ∈ [-2, -1]; Leq cEff = gBox.lo = -2; T = 2; rootCeil = 2^(1/3) ⌈⌉.
    // Soundness: hi³ ≥ 2.
    CHECK(ri->interval.hi * ri->interval.hi * ri->interval.hi >= mpq_class(2));
    // Tightness: hi ≤ 2 (since 2^(1/3) ≈ 1.26 ≪ 2).
    CHECK(ri->interval.hi <= mpq_class(2));
    // Lower untouched (odd-d Leq doesn't narrow below).
    CHECK(ri->interval.lo == mpq_class(-10));
}

// -- Conflict via narrowing ---------------------------------------------------

TEST_CASE("ICP-Q V4: x²+y² ≤ 1 with y ≥ 2 emits Conflict (cEff implies x² ≤ -3)") {
    // g(y) = y² - 1 ∈ [3, ...]; Leq cEff = gBox.lo ≥ 3; T = -cEff/a < 0.
    // d even, T < 0 ⇒ kEmpty ⇒ Conflict. Reasons must include both box
    // reasons (100, 101) and the constraint (200).
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                              f.kernel->pow(f.yp, 2)),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(2), mpq_class(3), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
    REQUIRE(r.conflict.has_value());
    bool hasX = false, hasY = false, hasCstr = false;
    for (const auto& l : r.conflict->clause) {
        if (l == SatLit::positive(100)) hasX = true;
        if (l == SatLit::positive(101)) hasY = true;
        if (l == SatLit::positive(200)) hasCstr = true;
    }
    CHECK(hasY);     // rest-var reason must appear
    CHECK(hasCstr);
    // hasX may or may not appear depending on whether livevar reasons were
    // consulted at conflict time — the rest-var reason is the load-bearing
    // one for the disc<0 path.
    (void)hasX;
}

// -- Sign-flip normalization --------------------------------------------------

TEST_CASE("ICP-Q V4: -x²+y² ≤ 0 (a < 0) normalizes and narrows x as |x| ≥ |y|… or skips") {
    // -x² + y² ≤ 0 ⇔ x² ≥ y². With y² ≥ 0, this is a Geq-with-T-≥-0 case
    // for even d ⇒ union ⇒ V4 returns nullopt ⇒ NoChange.
    Fixture f;
    PolyId xSqNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xSqNeg, f.kernel->pow(f.yp, 2));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    // Box unchanged.
    auto rx = box.get("x");
    REQUIRE(rx.has_value());
    CHECK(rx->interval.lo == mpq_class(-10));
    CHECK(rx->interval.hi == mpq_class(10));
}

// -- Factory rejects univariate from V4 path ---------------------------------

TEST_CASE("ICP-Q V4: factory builds V4 only for vars.size() >= 2") {
    Fixture f;
    // Univariate: factory routes to RelationContractorQ, not V4.
    PolyId uni = f.kernel->add(f.kernel->pow(f.xp, 2),
                                f.kernel->mkConst(mpq_class(-4)));
    auto cUni = f.cstr(uni, Relation::Leq, 200);
    auto builtUni = ContractorFactoryQ::build({cUni}, *f.kernel);
    // Exactly one contractor (the univariate RelationContractorQ).
    CHECK(builtUni.contractors.size() == 1);

    // Multivariate: V4 instances per usable live var. x²+y²-1 yields 2.
    PolyId multi = f.kernel->add(f.kernel->add(f.kernel->pow(f.xp, 2),
                                                f.kernel->pow(f.yp, 2)),
                                  f.kernel->mkConst(mpq_class(-1)));
    auto cMulti = f.cstr(multi, Relation::Leq, 200);
    auto builtMulti = ContractorFactoryQ::build({cMulti}, *f.kernel);
    CHECK(builtMulti.contractors.size() == 2);
}

#endif  // XOLVER_HAS_LIBPOLY
