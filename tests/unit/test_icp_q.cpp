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

#endif  // XOLVER_HAS_LIBPOLY
