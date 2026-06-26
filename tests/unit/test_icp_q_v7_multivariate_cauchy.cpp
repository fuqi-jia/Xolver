// V7 — MultivariateCauchyContractorQ tests.
//
// Shape: a · liveVar^d + Σ_{0 ≤ k < d} B_k(rest) · liveVar^k  rel  0
// where a is scalar, d ≥ 3 (V5b handles d=2), and at least one k < d
// has a non-trivial B_k contribution. Interval Cauchy bound on roots.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/kernel/icp/IcpEngineQ.h"
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"
#include "theory/arith/kernel/icp/contractors/MultivariateCauchyContractorQ.h"
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

TEST_CASE("ICP-Q V7: x³ + y·x² + 1 detects on x (mid-degree mixed term)") {
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xCube, yXSq),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    MultivariateCauchyContractorQ cx(c, *f.kernel, "x");
    CHECK(cx.isUsable());
}

TEST_CASE("ICP-Q V7: x² + y·x + 1 declines (degree 2 — V5b territory)") {
    Fixture f;
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId yX = f.kernel->mul(f.yp, f.xp);
    PolyId poly = f.kernel->add(f.kernel->add(xSq, yX),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    MultivariateCauchyContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

TEST_CASE("ICP-Q V7: x³ + y² declines (V4 territory — no mid-degree mixed)") {
    Fixture f;
    PolyId poly = f.kernel->add(f.kernel->pow(f.xp, 3),
                                 f.kernel->pow(f.yp, 2));
    auto c = f.cstr(poly, Relation::Leq, 200);

    MultivariateCauchyContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

TEST_CASE("ICP-Q V7: x³·y + 1 declines (mixed live^d, out of V7 scope)") {
    Fixture f;
    PolyId xCubeY = f.kernel->mul(f.kernel->pow(f.xp, 3), f.yp);
    PolyId poly = f.kernel->add(xCubeY, f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    MultivariateCauchyContractorQ cx(c, *f.kernel, "x");
    CHECK_FALSE(cx.isUsable());
}

// -- Narrowing — Eq ----------------------------------------------------------

TEST_CASE("ICP-Q V7: x³ + y·x² - 1 = 0 with y ∈ [1, 2] brackets x via Cauchy") {
    // B_2 = y ∈ [1, 2], max|B_2| = 2. B_0 = -1, max|B_0| = 1. M = 1 + 2/1 = 3.
    // For Eq, bracket [-3, 3].
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xCube, yXSq),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-3));
    CHECK(ri->interval.hi <= mpq_class(3));
    // Soundness: poly has a real root somewhere small (x³+yx²=1 has
    // x ≈ 0.5 to 0.7 for y ∈ [1, 2]). Must be inside bracket.
    CHECK(ri->interval.lo <= mpq_class(0));
    CHECK(ri->interval.hi >= mpq_class(1));
}

// -- Narrowing — Leq with odd d (upper bound only) --------------------------

TEST_CASE("ICP-Q V7: x³ + y·x² + z·x - 4 ≤ 0 with y, z ∈ [1, 2] narrows x ≤ 5") {
    // M = 1 + max(2/1, 2/1, 4/1) = 5. Odd d=3 Leq → x ≤ 5.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId zX = f.kernel->mul(f.zp, f.xp);
    PolyId poly = f.kernel->add(
        f.kernel->add(f.kernel->add(xCube, yXSq), zX),
        f.kernel->mkConst(mpq_class(-4)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);
    f.setBox(box, "z", mpq_class(1), mpq_class(2), 102);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(5));
    CHECK(ri->interval.lo == mpq_class(-100));  // odd-d Leq: lower untouched
}

// -- Narrowing — Eq with even d (full bracket) ------------------------------

TEST_CASE("ICP-Q V7: x⁴ + y·x² + z = 0 with y ∈ [1, 2], z ∈ [-1, 1] brackets x") {
    // d=4 even. B_2 = y ∈ [1,2] max=2. B_0 = z ∈ [-1,1] max=1. M = 1 + 2 = 3.
    // For Eq, bracket [-3, 3].
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xPow4, yXSq), f.zp);
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);
    f.setBox(box, "z", mpq_class(-1), mpq_class(1), 102);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-3));
    CHECK(ri->interval.hi <= mpq_class(3));
}

// -- Sign-flip (a < 0) -------------------------------------------------------

TEST_CASE("ICP-Q V7: -x³ - y·x² + 4 ≥ 0 with y ∈ [1, 2] normalizes to a > 0 Leq") {
    // After normalization: x³ + y·x² - 4 ≤ 0. Same M = 1 + max(2/1, 4/1) = 5.
    // Odd-d Leq → x ≤ 5.
    Fixture f;
    PolyId xCubeNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                     f.kernel->pow(f.xp, 3));
    PolyId yXSqNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                    f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2)));
    PolyId poly = f.kernel->add(f.kernel->add(xCubeNeg, yXSqNeg),
                                 f.kernel->mkConst(mpq_class(4)));
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(5));
    CHECK(ri->interval.lo == mpq_class(-100));
}

// -- Geq, a > 0, d even → decline (union) -----------------------------------

TEST_CASE("ICP-Q V7: x⁴ + y·x² + 1 ≥ 0 with y ∈ [1, 2] declines (union)") {
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xPow4, yXSq),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);
    f.setBox(box, "y", mpq_class(1), mpq_class(2), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-100));
    CHECK(ri->interval.hi == mpq_class(100));
}

// -- Conflict via narrowing -------------------------------------------------

TEST_CASE("ICP-Q V7: x³ + y·x² + 100 ≤ 0 with y ∈ [-1, 1], x ∈ [50, 60] Conflict") {
    // x narrowed via Cauchy: M = 1 + max(1, 100) = 101. Odd-d Leq → x ≤ 101.
    // But xBox = [50, 60] is already inside. So no narrowing... but the
    // polynomial evaluated over [50, 60] is huge positive. V1 should detect
    // violation. Let's check that the result is Conflict (via V1) regardless.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xCube, yXSq),
                                 f.kernel->mkConst(mpq_class(100)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(50), mpq_class(60), 100);
    f.setBox(box, "y", mpq_class(-1), mpq_class(1), 101);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- Factory routing --------------------------------------------------------

TEST_CASE("ICP-Q V7: factory routes x³+y·x²+1 multivariate to V7 for x") {
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId yXSq = f.kernel->mul(f.yp, f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xCube, yXSq),
                                 f.kernel->mkConst(mpq_class(1)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    // For x: V4 declines (yx² mixed), V5b declines (d=3), V5c declines
    // (has x²), V7 accepts. For y: only y^1 appears (in yx², mixed live);
    // V5c can handle the y-as-live case (no live^2 for y). So:
    //   For x: V7 → 1
    //   For y: V5c → 1
    // Total: 2.
    CHECK(built.contractors.size() == 2);
}

#endif  // XOLVER_HAS_LIBPOLY
