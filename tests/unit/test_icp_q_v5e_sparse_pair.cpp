// V5e — Sparse-pair Eq narrowing for `a·x^d + b·x^(d-p) = 0`.
//
// Factor: x^(d-p) · (a·x^p + b). Roots = {0} ∪ {roots of a·x^p + b}.
// Reduces to V3b-style root math on a degree-p monomial+constant.
//
// Also exercises V5d's relaxed `nonZero >= 2` guard for sparse Leq/Geq.

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

// -- Eq sparse pair: odd p (single second-factor root) ----------------------

TEST_CASE("ICP-Q V5e: x³ + x² = 0 brackets x to [-1, 0]") {
    // Factor: x²·(x + 1) = 0 ⇒ x ∈ {-1, 0}. p = 1, T = -1 → second root = -1.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 3),
                                 f.kernel->pow(f.xp, 2));
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
    // Tight bracket: includes both roots {-1, 0}.
    CHECK(ri->interval.lo == mpq_class(-1));
    CHECK(ri->interval.hi == mpq_class(0));
}

TEST_CASE("ICP-Q V5e: x³ + 8·x² = 0 brackets x to [-8, 0]") {
    // x²(x+8)=0 ⇒ roots 0, -8.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId eightXSq = f.kernel->mul(f.kernel->mkConst(mpq_class(8)),
                                     f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xCube, eightXSq);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-8));
    CHECK(ri->interval.hi == mpq_class(0));
}

// -- Eq sparse pair: even p (two second-factor roots) -----------------------

TEST_CASE("ICP-Q V5e: x³ - x = 0 brackets x to [-1, 1]") {
    // Factor: x(x² - 1) = 0 ⇒ roots 0, ±1. p = 2 (even), T = 1, ±√1 = ±1.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId negX = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)), f.xp);
    PolyId poly = f.kernel->add(xCube, negX);
    auto c = f.cstr(poly, Relation::Eq, 200);

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

TEST_CASE("ICP-Q V5e: x⁴ - x² = 0 brackets x to [-1, 1]") {
    // x²(x² - 1) = 0 ⇒ roots 0, ±1.
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId negXSq = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xPow4, negXSq);
    auto c = f.cstr(poly, Relation::Eq, 200);

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

// -- Eq sparse pair: even p, T < 0 (only x = 0 root) ------------------------

TEST_CASE("ICP-Q V5e: x⁴ + x² = 0 brackets x to {0}") {
    // x²(x² + 1) = 0. Second factor x²+1 has no real roots ⇒ only x = 0.
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(xPow4, xSq);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(0));
}

// -- Sign normalization: a < 0 ----------------------------------------------

TEST_CASE("ICP-Q V5e: -x³ + x² = 0 brackets x to [0, 1] (sign-flip works)") {
    // -x³ + x² = 0 ⇒ x²(-x + 1) = 0 ⇒ roots 0, 1.
    // Internally Eq is sign-invariant: -b/a where a = -1, b = 1 ⇒ T = -1/-1 = 1.
    Fixture f;
    PolyId xCubeNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                     f.kernel->pow(f.xp, 3));
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(xCubeNeg, xSq);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(1));
}

// -- Decline cases -----------------------------------------------------------

TEST_CASE("ICP-Q V5e: x³ + x² + 1 = 0 (non-zero constant) declines V5e") {
    // V5e requires constant = 0. With non-zero constant, V5e declines and
    // V5d Cauchy fires: M = 1 + max(1, 0, 1)/1 = 2. Bracket [-2, 2].
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(f.kernel->add(xCube, xSq),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // V5d Cauchy [-2, 2].
    CHECK(ri->interval.lo >= mpq_class(-2));
    CHECK(ri->interval.hi <= mpq_class(2));
}

TEST_CASE("ICP-Q V5e: pure x³ = 0 declines (V3a's territory)") {
    // V3a catches pure monomial Eq first (returns {0} if 0 ∈ xBox).
    // V5e never gets a chance.
    Fixture f;
    PolyId poly = f.kernel->pow(f.xp, 3);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-10), mpq_class(10), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(0));
}

// -- V5d relaxed guard catches sparse Leq fallback --------------------------

TEST_CASE("ICP-Q V5d (relaxed): x³ + x² ≤ 0 narrows x ≤ 2 via Cauchy") {
    // V5e declines (only Eq). V5d's nonZero >= 2 guard now catches this.
    // M = 1 + max(1, 0, 0) = 2. Odd-d Leq → upper x ≤ 2.
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 3),
                                 f.kernel->pow(f.xp, 2));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(2));
    // Lower untouched (odd-d Leq).
    CHECK(ri->interval.lo == mpq_class(-100));
}

// -- Higher-degree sparse pair ----------------------------------------------

TEST_CASE("ICP-Q V5e: x⁵ + 32·x² = 0 brackets x to outward bracket containing roots") {
    // x²(x³ + 32) = 0 ⇒ roots 0 and x³ = -32 ⇒ x = -∛32 ≈ -3.175.
    // Outward bracket: lo ≤ -3.175 (∛32 rounded UP, negated) and hi ≥ 0.
    Fixture f;
    PolyId xPow5 = f.kernel->pow(f.xp, 5);
    PolyId thirtyTwoXSq = f.kernel->mul(f.kernel->mkConst(mpq_class(32)),
                                         f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(xPow5, thirtyTwoXSq);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Soundness: lo³ ≤ -32 (outward — more negative).
    mpq_class lo3 = ri->interval.lo * ri->interval.lo * ri->interval.lo;
    CHECK(lo3 <= mpq_class(-32));
    // 0 included.
    CHECK(ri->interval.hi >= mpq_class(0));
    // Tightness: lo ≥ -10 (since ∛32 ≈ 3.175, not 100).
    CHECK(ri->interval.lo >= mpq_class(-10));
    CHECK(ri->interval.hi <= mpq_class(1));
}

#endif  // XOLVER_HAS_LIBPOLY
