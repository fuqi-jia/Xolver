// XOLVER_NRA_ICP — Q-side engine and RelationContractorQ semantics.
//
// Each test seeds a closed-interval ReasonedBoxQ, builds a univariate
// IcpConstraint, runs IcpEngineQ, and checks the soundness contract:
//   - Conflict only when polyInterval definitively excludes the relation.
//   - NoChange when the box still admits a value satisfying the relation.
//   - Conflict reasons union the constraint reason with the box's bound
//     reasons (this is what makes the resulting TheoryConflict sound).

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
    PolyId xpoly;

    Fixture() : kernel(createPolynomialKernel()) {
        x = kernel->getOrCreateVar("x");
        xpoly = kernel->mkVar(x);
    }

    // Build poly = x^n + constant.
    PolyId xPowPlus(uint32_t n, long c) {
        PolyId p = kernel->pow(xpoly, n);
        if (c != 0) p = kernel->add(p, kernel->mkConst(mpq_class(c)));
        return p;
    }

    // Build poly = a·x² + b·x + c (for V2 quadratic-narrowing tests).
    PolyId quad(long a, long b, long c) {
        PolyId x2 = kernel->pow(xpoly, 2);
        PolyId result = (a == 1) ? x2
                                  : kernel->mul(kernel->mkConst(mpq_class(a)), x2);
        if (b != 0) {
            PolyId bx = (b == 1) ? xpoly
                                  : kernel->mul(kernel->mkConst(mpq_class(b)), xpoly);
            result = kernel->add(result, bx);
        }
        if (c != 0) result = kernel->add(result, kernel->mkConst(mpq_class(c)));
        return result;
    }

    // Build poly = a·x^d (pure monomial, for V3a tests).
    PolyId monomial(long a, uint32_t d) {
        PolyId xd = kernel->pow(xpoly, d);
        if (a == 1) return xd;
        return kernel->mul(kernel->mkConst(mpq_class(a)), xd);
    }

    static SatLit lit(unsigned id) { return SatLit::positive(id); }

    ReasonedBoxQ box(const mpq_class& lo, const mpq_class& hi, unsigned r) {
        ReasonedBoxQ b;
        b.set("x", ReasonedIntervalQ{IntervalQ{lo, hi}, {lit(r)}});
        return b;
    }

    IcpConstraint cstr(PolyId p, Relation rel, unsigned r) {
        return IcpConstraint{std::nullopt, p, rel, lit(r), TheoryId::NRA};
    }
};

} // namespace

TEST_CASE("ICP-Q: x^2 - 3 <= 0 with x in [2,3] is unsat — every value yields polyInterval [1,6] > 0") {
    Fixture f;
    auto b = f.box(2, 3, /*boxReason=*/100);
    auto c = f.cstr(f.xPowPlus(2, -3), Relation::Leq, /*cstrReason=*/200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(built.contractors.size() == 1);

    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::Conflict);
    REQUIRE(r.conflict.has_value());
    // Soundness: both the box reason and the constraint reason must appear.
    const auto& lits = r.conflict->clause;
    bool hasBox = false, hasCstr = false;
    for (const auto& l : lits) {
        if (l == SatLit::positive(100)) hasBox = true;
        if (l == SatLit::positive(200)) hasCstr = true;
    }
    CHECK(hasBox);
    CHECK(hasCstr);
}

TEST_CASE("ICP-Q: x^2 - 10 <= 0 with x in [2,3] is sat — polyInterval [-6,-1] ≤ 0, NoChange") {
    Fixture f;
    auto b = f.box(2, 3, 100);
    auto c = f.cstr(f.xPowPlus(2, -10), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    CHECK_FALSE(r.conflict.has_value());
}

TEST_CASE("ICP-Q: x^3 = 0 with x in [1,2] is unsat — odd power keeps strict sign on [1,8]") {
    Fixture f;
    auto b = f.box(1, 2, 100);
    auto c = f.cstr(f.xPowPlus(3, 0), Relation::Eq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("ICP-Q: x^2 + 1 >= 0 with x in [-5, 5] is sat — sound NoChange (no spurious conflict)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.xPowPlus(2, 1), Relation::Geq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
}

TEST_CASE("ICP-Q: Lt soundness — x^2 - 4 < 0 with x in [2,3], polyInterval [0,5]; lo>=0 ⇒ definite violation") {
    Fixture f;
    auto b = f.box(2, 3, 100);
    auto c = f.cstr(f.xPowPlus(2, -4), Relation::Lt, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // x^2 - 4 ∈ [0, 5]; Lt requires strict < 0, but 0 is achievable, so Conflict.
    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("ICP-Q: multi-var atom is skipped by factory (V1 univariate-only)") {
    Fixture f;
    VarId y = f.kernel->getOrCreateVar("y");
    PolyId yp = f.kernel->mkVar(y);
    PolyId xy = f.kernel->mul(f.xpoly, yp);
    auto c = f.cstr(xy, Relation::Eq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    CHECK(built.contractors.empty());  // multi-var rejected before contractor build
}

TEST_CASE("ICP-Q: factory builds RelationContractorQ for univariate degree-2") {
    Fixture f;
    auto c = f.cstr(f.xPowPlus(2, -3), Relation::Leq, 200);
    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(built.contractors.size() == 1);
    auto vars = built.contractors[0]->vars();
    REQUIRE(vars.size() == 1);
    CHECK(vars[0] == "x");
}

// -- V2 quadratic narrowing --------------------------------------------------

TEST_CASE("ICP-Q V2: x²-4 ≤ 0 with x ∈ [-10,10] narrows to [-2,2] (exact roots)") {
    Fixture f;
    auto b = f.box(-10, 10, 100);
    auto c = f.cstr(f.quad(1, 0, -4), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    REQUIRE(built.contractors.size() == 1);

    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // Disc = 16 → exact roots ±2 → box narrows to [-2, 2] then fixpoints.
    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-2));
    CHECK(ri->interval.hi == mpq_class(2));
}

TEST_CASE("ICP-Q V2: x²-5 ≤ 0 with x ∈ [-10,10] narrows to outward-rounded [-√5, √5]") {
    Fixture f;
    auto b = f.box(-10, 10, 100);
    auto c = f.cstr(f.quad(1, 0, -5), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    // Soundness: lo ≤ -√5 and hi ≥ √5. Verify via squaring (lo² ≥ 5, hi² ≥ 5).
    CHECK(ri->interval.lo * ri->interval.lo >= mpq_class(5));
    CHECK(ri->interval.hi * ri->interval.hi >= mpq_class(5));
    // Sanity: not absurdly loose (tightness ≪ 2^-30 of √5).
    CHECK(ri->interval.hi - mpq_class(0) <= mpq_class(3));
    CHECK(ri->interval.lo >= mpq_class(-3));
}

TEST_CASE("ICP-Q V2: x² + 2x + 5 ≤ 0 — V2 disc=-16 < 0 conflict (V1 inconclusive on [-10,10])") {
    // Vertex at x = -1, value 4 > 0 ⇒ globally positive ⇒ Leq unsat.
    // V1's polyInterval on [-10, 10] = [0,100] + [-20,20] + 5 = [-15, 125],
    // lo = -15 ≤ 0 ⇒ V1 doesn't detect. V2's discriminant test does.
    Fixture f;
    auto b = f.box(-10, 10, 100);
    auto c = f.cstr(f.quad(1, 2, 5), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::Conflict);
    REQUIRE(r.conflict.has_value());
    bool hasCstr = false;
    for (const auto& l : r.conflict->clause) {
        if (l == SatLit::positive(200)) hasCstr = true;
    }
    CHECK(hasCstr);
}

TEST_CASE("ICP-Q V2: x²-2x-3 ≤ 0 with x ∈ [-10,10] narrows to [-1,3] (b ≠ 0)") {
    Fixture f;
    auto b = f.box(-10, 10, 100);
    // disc = 4 + 12 = 16, roots (2±4)/2 = -1, 3.
    auto c = f.cstr(f.quad(1, -2, -3), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-1));
    CHECK(ri->interval.hi == mpq_class(3));
}

TEST_CASE("ICP-Q V2: Lt narrowing — x² - 4 < 0 with x ∈ [-10,10] narrows to [-2,2]") {
    // V1: polyInterval [-4, 96]; Lt's `lo ≥ 0` check is -4 ≥ 0 ⇒ false ⇒
    // no V1 conflict. V2 narrows on the closed over-approximation [-2, 2].
    // Strict relation correctness: feasible set is (-2, 2), our closed
    // over-approx admits ±2 too; sound — we never drop a true solution.
    Fixture f;
    auto b = f.box(-10, 10, 100);
    auto c = f.cstr(f.quad(1, 0, -4), Relation::Lt, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-2));
    CHECK(ri->interval.hi == mpq_class(2));
    // After narrowing, V1's re-fire on [-2, 2] sees polyInterval [-4, 0];
    // Lt's `lo ≥ 0` is false (-4 ≥ 0), so no V1 conflict. Engine returns
    // NoChange at fixpoint.
    CHECK(r.status == IcpStatus::NoChange);
}

TEST_CASE("ICP-Q V2: Geq is not narrowed (V2 covers Leq/Lt only)") {
    // x² - 100 ≥ 0 with x ∈ [-3, 3]: feasible set is (-∞, -10] ∪ [10, ∞),
    // not representable by a single IntervalQ. V1: polyInterval [-100, -91],
    // hi < 0 ⇒ Geq violated ⇒ Conflict. V2 must not even attempt narrowing.
    // We assert Conflict (from V1) and that the box reasons participate.
    Fixture f;
    auto b = f.box(-3, 3, 100);
    auto c = f.cstr(f.quad(1, 0, -100), Relation::Geq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("ICP-Q V2: a < 0 case is skipped (single-interval representation fails)") {
    // -x² + 4 ≤ 0 (i.e., x² ≥ 4) with x ∈ [-10, 10]: feasible (-∞, -2] ∪ [2, ∞).
    // V2 must skip (a = -1 < 0). V1: polyInterval evaluated as -x² + 4 over
    // [-10, 10]: -x² ∈ [-100, 0] (k=2, contains zero ⇒ [0, max(100,100)] for x²
    // → negate ⇒ [-100, 0]); plus 4 ⇒ [-96, 4]. lo=-96 ≤ 0, hi=4 ≥ 0, so
    // neither Leq violation nor narrowing applies ⇒ NoChange.
    Fixture f;
    auto b = f.box(-10, 10, 100);
    auto c = f.cstr(f.quad(-1, 0, 4), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    // Box must be unchanged (no V2 narrowing).
    CHECK(ri->interval.lo == mpq_class(-10));
    CHECK(ri->interval.hi == mpq_class(10));
}

TEST_CASE("ICP-Q V2: Lt unsat — x² < 0 detected by V1 sign-uniform check") {
    // V1's polyInterval(x², [-1,1]) = [0, 1]; for Lt the predicate is
    // `lo ≥ 0` ⇒ 0 ≥ 0 ⇒ Conflict. V2 never runs (V1 short-circuits). The
    // value here is asserting V2 wiring didn't regress V1's existing
    // strict-sign reasoning on a degenerate disc=0 case.
    Fixture f;
    auto b = f.box(-1, 1, 100);
    auto c = f.cstr(f.quad(1, 0, 0), Relation::Lt, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::Conflict);
}

// -- V3a pure-monomial narrowing (degree ≥ 3) --------------------------------

TEST_CASE("ICP-Q V3a: x^3 ≤ 0 with x ∈ [-5,5] narrows upper to 0 (odd d, Leq)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.monomial(1, 3), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // sign(x^3) = sign(x); Leq ⇒ x ≤ 0.
    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-5));
    CHECK(ri->interval.hi == mpq_class(0));
}

TEST_CASE("ICP-Q V3a: 2x^5 > 0 with x ∈ [-5,5] narrows lower to 0 (odd d, Gt)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.monomial(2, 5), Relation::Gt, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // x^5 > 0 ⇔ x > 0; closed over-approx ⇒ x ∈ [0, 5].
    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(5));
}

TEST_CASE("ICP-Q V3a: x^4 ≤ 0 with x ∈ [-5,5] narrows to {0} (even d, Leq)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.monomial(1, 4), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // Even d, a > 0: x^d ≤ 0 ⇔ x = 0; intersect with xBox = {0}.
    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(0));
}

TEST_CASE("ICP-Q V3a: x^4 < 0 is unsat regardless of box (even d, Lt)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.monomial(1, 4), Relation::Lt, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // V1 catches first: polyInterval(x⁴, [-5,5]) = [0, 625]; Lt's lo ≥ 0 ⇒
    // Conflict. The test asserts no regression: even-d Lt remains unsat.
    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("ICP-Q V3a: -x^3 ≤ 0 normalizes a > 0 then narrows lower to 0 (sign flip)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    // a = -1, d = 3 (odd). After normalization: a > 0, rel = Geq ⇒ x ≥ 0.
    auto c = f.cstr(f.monomial(-1, 3), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(5));
}

TEST_CASE("ICP-Q V3a: x^3 = 0 with x ∈ [-5,5] narrows to {0} (odd d, Eq)") {
    Fixture f;
    auto b = f.box(-5, 5, 100);
    auto c = f.cstr(f.monomial(1, 3), Relation::Eq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(0));
    CHECK(ri->interval.hi == mpq_class(0));
}

TEST_CASE("ICP-Q V3a: x^4 ≤ 0 with x ∈ [2,5] (0 ∉ box) is unsat") {
    Fixture f;
    auto b = f.box(2, 5, 100);
    auto c = f.cstr(f.monomial(1, 4), Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    // V1: polyInterval = [16, 625], lo > 0 ⇒ Leq Conflict. (V3a would also
    // emit Conflict via {0} ∩ [2,5] = empty, but V1 fires first.)
    CHECK(r.status == IcpStatus::Conflict);
    REQUIRE(r.conflict.has_value());
    bool hasBox = false, hasCstr = false;
    for (const auto& l : r.conflict->clause) {
        if (l == SatLit::positive(100)) hasBox = true;
        if (l == SatLit::positive(200)) hasCstr = true;
    }
    CHECK(hasBox);
    CHECK(hasCstr);
}

TEST_CASE("ICP-Q V3a: non-monomial with degree ≥ 3 falls through (V3 not applicable)") {
    // x³ - 1 ≤ 0 is degree 3 but has a nonzero constant ⇒ tryNarrowPureMonomial
    // returns nullopt. V1's polyInterval over [-5, 5] is x³ ∈ [-125, 125], minus
    // 1 ⇒ [-126, 124]; Leq: lo ≤ 0, no V1 conflict. So we expect NoChange and
    // the box unchanged — confirming V3a doesn't over-reach to mixed polynomials.
    Fixture f;
    auto b = f.box(-5, 5, 100);
    PolyId p = f.kernel->add(f.monomial(1, 3),
                              f.kernel->mkConst(mpq_class(-1)));
    auto c = f.cstr(p, Relation::Leq, 200);

    auto built = ContractorFactoryQ::build({c}, *f.kernel);
    IcpConfig cfg;
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, b, cfg);

    CHECK(r.status == IcpStatus::NoChange);
    auto ri = b.get("x");
    REQUIRE(ri.has_value());
    CHECK(ri->interval.lo == mpq_class(-5));
    CHECK(ri->interval.hi == mpq_class(5));
}

#endif  // XOLVER_HAS_LIBPOLY
