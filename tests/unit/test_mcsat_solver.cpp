// Integration tests for the McsatSolver framework end-to-end.
//
// Confirms:
//   1. With an engine that always GiveUps, check() returns Unknown
//      (never UNSAT) — soundness floor.
//   2. With NlsatEngine attached, an x = 0 assertion routes through
//      pickValue successfully and check() returns Consistent.
//   3. Backtrack clears framework-side pending state.

#include "experimental/mcsat/McsatSolver.h"
#include "theory/arith/logics/nia/mcsat/NiaMcsatEngine.h"
#include "theory/arith/logics/nra/nlsat/NlsatEngine.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryPropagatorCallbacks.h"  // TheoryLemmaStorage
#include "util/RealValue.h"

#include <doctest/doctest.h>
#include <memory>

using namespace xolver;

namespace {

class AlwaysGiveUpEngine : public mcsat::MCSatEngine {
public:
    void reset() override {}
    void onAssertAtom(const TheoryAtomRecord&, bool, int, SatLit) override {}
    void onBacktrack(int) override {}
    VarId pickNextVar(const mcsat::MCSatTrail&) override { return 1; }
    mcsat::ValueChoice pickValue(VarId,
                                 const mcsat::MCSatTrail&) override {
        return mcsat::ValueChoice::giveUp("test: always give up");
    }
    std::vector<SatLit> explainConflict(
        const mcsat::MCSatTrail&,
        const std::vector<TheoryAtomRecord>&) override { return {}; }
    bool validateModel(const mcsat::MCSatTrail&,
                       TheorySolver::TheoryModel&) override { return false; }
};

TheoryAtomRecord trivialPolyAtom(PolyId p, Relation rel, RealValue rhs,
                                 SatVar satVar = 1) {
    TheoryAtomRecord rec;
    rec.satVar = satVar;
    rec.theory = TheoryId::NRA;
    rec.isDynamic = false;
    rec.exprId = 0;
    PolynomialAtomPayload payload;
    payload.poly = p;
    payload.rel = rel;
    payload.rhs = std::move(rhs);
    rec.payload = std::move(payload);
    return rec;
}

class StubLemmaStorage : public TheoryLemmaStorage {
public:
    bool contains(const TheoryLemma&) const override { return false; }
    bool insertIfNew(const TheoryLemma&) override { return true; }
};

} // namespace

TEST_CASE("McsatSolver: returns Unknown when engine always gives up") {
    McsatSolver solver;
    solver.setEngine(std::make_unique<AlwaysGiveUpEngine>(), TheoryId::NRA);

    StubLemmaStorage db;
    auto r = solver.check(db);
    // Never UNSAT from a GiveUp.
    CHECK(r.kind == TheoryCheckResult::Kind::Unknown);
}

TEST_CASE("McsatSolver: returns Unknown with no engine attached") {
    McsatSolver solver;
    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Unknown);
}

TEST_CASE("McsatSolver: NlsatEngine drives a trivial SAT path") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    // Assert x >= 0 directly on the framework so the engine sees it.
    auto atom = trivialPolyAtom(xPoly, Relation::Geq, RealValue::fromInt(0));
    solver.assertLit(atom, /*value=*/true, /*level=*/1, SatLit{1, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    // pickValue should return 0 for x; validateModel sees x=0, returns
    // true; framework reports Consistent (sat-shape).
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver: NiaMcsatEngine drives a trivial SAT path") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
    engine->setKernel(kernel.get());

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NIA);

    auto atom = trivialPolyAtom(xPoly, Relation::Geq, RealValue::fromInt(0));
    atom.theory = TheoryId::NIA;
    solver.assertLit(atom, true, 1, SatLit{1, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver: backtrack clears pending state") {
    McsatSolver solver;
    solver.setEngine(std::make_unique<AlwaysGiveUpEngine>(), TheoryId::NRA);

    // First check parks an Unknown (engine always gives up). After
    // backtrack to level 0 the framework state is clean again.
    StubLemmaStorage db;
    auto r1 = solver.check(db);
    CHECK(r1.kind == TheoryCheckResult::Kind::Unknown);

    solver.backtrackToLevel(0);
    auto r2 = solver.check(db);
    CHECK(r2.kind == TheoryCheckResult::Kind::Unknown);
    // No stale TheoryConflict leaked across the boundary.
}
