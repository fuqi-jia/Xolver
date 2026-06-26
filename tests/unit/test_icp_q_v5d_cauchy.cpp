// V5d — Cauchy-bound narrowing for mixed-degree univariate.
//
// Fires when V2/V3a/V3b decline AND the polynomial has ≥ 3 non-zero
// coefficients. Soundness: all real roots satisfy |x| ≤ M where
// M = 1 + max(|aᵢ/aₙ|). For Eq, bracket [-M, M] contains the root set.
// For Leq (a > 0): even-d → bracket [-M, M]; odd-d → upper bound x ≤ M.
// Geq symmetric. Loose but always sound.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/kernel/icp/IcpEngineQ.h"
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"
#include "theory/arith/kernel/icp/contractors/RelationContractorQ.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/kernel/interval/ReasonedBoxQ.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
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

// -- Eq dense univariate -----------------------------------------------------

TEST_CASE("ICP-Q V5d: x³ + x − 5 = 0 narrows x to Cauchy bracket [-6, 6]") {
    // coeffs [1, 0, 1, -5]: nonZero count = 3 (1, 1, -5). V3a/V3b decline
    // (intermediate coeff x¹ = 1 nonzero). V5d Cauchy:
    // M = 1 + max(|0|/1, |1|/1, |-5|/1) = 1 + 5 = 6.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId poly = f.kernel->add(f.kernel->add(xCube, f.xp),
                                 f.kernel->mkConst(mpq_class(-5)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(!built.contractors.empty());
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // Bracket should be [-6, 6] (tighter than [-100, 100]).
    CHECK(ri->interval.lo >= mpq_class(-6));
    CHECK(ri->interval.hi <= mpq_class(6));
    // Soundness: the true root of x³ + x = 5 is ≈ 1.516, which must be
    // inside the bracket.
    CHECK(ri->interval.lo <= mpq_class(2));
    CHECK(ri->interval.hi >= mpq_class(2));
}

TEST_CASE("ICP-Q V5d: x⁴ + x² − 1 = 0 narrows to Cauchy bracket [-2, 2]") {
    // coeffs [1, 0, 1, 0, -1]: nonZero = 3. V3a/V3b decline. Cauchy:
    // M = 1 + max(0, 1, 0, 1) = 2.
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(f.kernel->add(xPow4, xSq),
                                 f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-2));
    CHECK(ri->interval.hi <= mpq_class(2));
    // Sanity: the actual roots are ±√((-1+√5)/2) ≈ ±0.786, well inside.
    CHECK(ri->interval.lo <= mpq_class(-1));
    CHECK(ri->interval.hi >= mpq_class(1));
}

// -- Leq with a > 0 even d (full bracket) ------------------------------------

TEST_CASE("ICP-Q V5d: x⁴ + x² − 4 ≤ 0 narrows to Cauchy bracket [-5, 5]") {
    // coeffs [1, 0, 1, 0, -4]. M = 1 + 4 = 5. Even d, so full bracket.
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(f.kernel->add(xPow4, xSq),
                                 f.kernel->mkConst(mpq_class(-4)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-5));
    CHECK(ri->interval.hi <= mpq_class(5));
    // Truth set is roughly |x| ≤ 1.25 — well inside our loose bracket.
    CHECK(ri->interval.lo <= mpq_class(-1));
    CHECK(ri->interval.hi >= mpq_class(1));
}

// -- Leq with a > 0 odd d (upper bound only) ---------------------------------

TEST_CASE("ICP-Q V5d: x³ + x − 5 ≤ 0 narrows upper only x ≤ 6") {
    // Odd d, a > 0: feasible set extends to -∞; only upper bound x ≤ M.
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId poly = f.kernel->add(f.kernel->add(xCube, f.xp),
                                 f.kernel->mkConst(mpq_class(-5)));
    auto c = f.cstr(poly, Relation::Leq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.hi <= mpq_class(6));
    // Lower unchanged (informative bound only on upper).
    CHECK(ri->interval.lo == mpq_class(-100));
}

// -- Geq with a > 0 odd d (lower bound only) ---------------------------------

TEST_CASE("ICP-Q V5d: x³ + x − 5 ≥ 0 narrows lower only x ≥ -6") {
    Fixture f;
    PolyId xCube = f.kernel->pow(f.xp, 3);
    PolyId poly = f.kernel->add(f.kernel->add(xCube, f.xp),
                                 f.kernel->mkConst(mpq_class(-5)));
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-6));
    CHECK(ri->interval.hi == mpq_class(100));
}

// -- Geq with a > 0 even d → union, V5d declines -----------------------------

TEST_CASE("ICP-Q V5d: x⁴ + x² − 4 ≥ 0 declines (union outside roots)") {
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId xSq = f.kernel->pow(f.xp, 2);
    PolyId poly = f.kernel->add(f.kernel->add(xPow4, xSq),
                                 f.kernel->mkConst(mpq_class(-4)));
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // No narrowing (V5d declines for even-d Geq).
    CHECK(ri->interval.lo == mpq_class(-100));
    CHECK(ri->interval.hi == mpq_class(100));
}

// -- Sign-flip (a < 0) -------------------------------------------------------

TEST_CASE("ICP-Q V5d: -x⁴ - x² + 4 ≥ 0 (a < 0 Geq) normalizes to a > 0 Leq → bracket") {
    // a = -1, d = 4. flipSign(Geq) = Leq. After normalization: a > 0 even-d Leq
    // → full Cauchy bracket [-M, M]. M = 1 + max(0, 1, 0, 4)/1 = 5.
    Fixture f;
    PolyId xPow4Neg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                     f.kernel->pow(f.xp, 4));
    PolyId xSqNeg = f.kernel->mul(f.kernel->mkConst(mpq_class(-1)),
                                   f.kernel->pow(f.xp, 2));
    PolyId poly = f.kernel->add(f.kernel->add(xPow4Neg, xSqNeg),
                                 f.kernel->mkConst(mpq_class(4)));
    auto c = f.cstr(poly, Relation::Geq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-5));
    CHECK(ri->interval.hi <= mpq_class(5));
}

// -- Decline cases (V3a/V3b shapes that should NOT reach V5d) ---------------

TEST_CASE("ICP-Q V5d: pure x⁴ = 16 is NOT routed to Cauchy (V3a/V3b handles it tighter)") {
    // V3a or V3b catches the pure-monomial / monomial+const case with a
    // tighter bracket [-2, 2] (exact 4th root). V5d would give [-17, 17].
    // After V5a, V3b's even-d Eq T>0 branch gives exact [-2, 2].
    Fixture f;
    PolyId xPow4 = f.kernel->pow(f.xp, 4);
    PolyId poly = f.kernel->add(xPow4, f.kernel->mkConst(mpq_class(-16)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    // V3b gives the tight bracket [-2, 2]; V5d would only get [-17, 17].
    CHECK(ri->interval.hi <= mpq_class(2));
    CHECK(ri->interval.lo >= mpq_class(-2));
}

// -- Direct unit test of tryNarrowCauchyBracket via engine, M computation --

TEST_CASE("ICP-Q V5d: 2x³ + 4x − 6 = 0 normalizes by leading coeff (M = 1 + 6/2 = 4)") {
    // Cauchy bound uses |a_i| / |a_d|. With a_d = 2:
    //   M = 1 + max(|0/2|, |4/2|, |-6/2|) = 1 + 3 = 4.
    Fixture f;
    PolyId twoXCube = f.kernel->mul(f.kernel->mkConst(mpq_class(2)),
                                     f.kernel->pow(f.xp, 3));
    PolyId fourX = f.kernel->mul(f.kernel->mkConst(mpq_class(4)), f.xp);
    PolyId poly = f.kernel->add(f.kernel->add(twoXCube, fourX),
                                 f.kernel->mkConst(mpq_class(-6)));
    auto c = f.cstr(poly, Relation::Eq, 200);

    ReasonedBoxQ box;
    f.setBox(box, "x", mpq_class(-100), mpq_class(100), 100);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);

    auto ri = box.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo >= mpq_class(-4));
    CHECK(ri->interval.hi <= mpq_class(4));
    // True root x = 1 (since 2 + 4 - 6 = 0) must be inside.
    CHECK(ri->interval.lo <= mpq_class(1));
    CHECK(ri->interval.hi >= mpq_class(1));
}

#endif  // XOLVER_HAS_LIBPOLY
