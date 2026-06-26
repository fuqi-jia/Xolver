// Multi-atom integration tests for the McsatSolver framework.
//
// These exercise the engines under more realistic conditions: several
// asserted atoms at once, backtrack across decisions, and confirm the
// soundness floor never produces UNSAT from heuristic failure.

#include "experimental/mcsat/McsatSolver.h"
#include "theory/arith/logics/nia/mcsat/NiaMcsatEngine.h"
#include "theory/arith/logics/nra/nlsat/NlsatEngine.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include "util/RealValue.h"

#include <doctest/doctest.h>
#include <memory>

using namespace xolver;

namespace {

TheoryAtomRecord polyAtom(PolyId p, Relation rel, RealValue rhs, SatVar sv,
                          TheoryId th = TheoryId::NRA) {
    TheoryAtomRecord rec;
    rec.satVar = sv;
    rec.theory = th;
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

TEST_CASE("McsatSolver+NRA: 0 <= x <= 5 finds x=0") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    solver.assertLit(polyAtom(xp, Relation::Geq, RealValue::fromInt(0), 1),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xp, Relation::Leq, RealValue::fromInt(5), 2),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver+NRA: x >= 1 AND x <= -1 → Conflict (Phase 6 explain)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    solver.assertLit(polyAtom(xp, Relation::Geq, RealValue::fromInt(1), 1),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xp, Relation::Leq, RealValue::fromInt(-1), 2),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    // Phase 6: NlsatEngine's simple-bound intersector detects the empty
    // interval and emits a theory-valid Conflict clause containing both
    // asserted literals. (Phase 5 had this returning Unknown — the
    // bound test was the trigger to add this analyzer.)
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("McsatSolver+NRA: x + y = 4 AND x - y = 2 → Consistent (DFS-driven backtrack)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));
    PolyId xMinusY = kernel->sub(kernel->mkVar(x), kernel->mkVar(y));

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    solver.assertLit(polyAtom(xPlusY, Relation::Eq, RealValue::fromInt(4), 1),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xMinusY, Relation::Eq, RealValue::fromInt(2), 2),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    // Limitation-(a) fix: NlsatEngine now runs a bounded DFS over the
    // candidate set on the first pickValue call. It finds x=3, y=1
    // (the unique solution), caches the full assignment, and returns
    // x=3 first then y=1. Result: Consistent. (Previous v0 returned
    // Unknown because the greedy candidate picker committed to x=0.)
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver+NRA: x = 3 AND x + y = 4 solves (candidate set covers it)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xp = kernel->mkVar(x);
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    // x = 3 fixes x immediately to 3 (no other value in the candidate
    // set satisfies the equality once we get to that candidate).
    solver.assertLit(polyAtom(xp, Relation::Eq, RealValue::fromInt(3), 1),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xPlusY, Relation::Eq, RealValue::fromInt(4), 2),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    // Engine picks x=0 first — x=0 survives the y-free atom but fails
    // the x=3 atom immediately. Tries x=1, fails. ... x=3, succeeds.
    // Then y=1 satisfies both, found.
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver+NIA: 0 <= x <= 5 finds x=0") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
    engine->setKernel(kernel.get());

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NIA);

    solver.assertLit(polyAtom(xp, Relation::Geq, RealValue::fromInt(0), 1, TheoryId::NIA),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xp, Relation::Leq, RealValue::fromInt(5), 2, TheoryId::NIA),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver+NIA: x >= 1 AND x <= -1 returns Unknown, never UNSAT") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
    engine->setKernel(kernel.get());

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NIA);

    solver.assertLit(polyAtom(xp, Relation::Geq, RealValue::fromInt(1), 1, TheoryId::NIA),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xp, Relation::Leq, RealValue::fromInt(-1), 2, TheoryId::NIA),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Unknown);
}

TEST_CASE("McsatSolver+NIA: x + y = 4 AND x - y = 2 → Consistent (DFS-driven)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));
    PolyId xMinusY = kernel->sub(kernel->mkVar(x), kernel->mkVar(y));

    auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
    engine->setKernel(kernel.get());

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NIA);

    solver.assertLit(polyAtom(xPlusY, Relation::Eq, RealValue::fromInt(4), 1, TheoryId::NIA),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xMinusY, Relation::Eq, RealValue::fromInt(2), 2, TheoryId::NIA),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    // Limitation-(a) fix mirrored into NIA: integer DFS finds x=3, y=1
    // and caches the full assignment. Sound — every atom validated.
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver+NIA: x = 3 AND x + y = 4 solves (candidate set covers it)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xp = kernel->mkVar(x);
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));

    auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
    engine->setKernel(kernel.get());

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NIA);

    solver.assertLit(polyAtom(xp, Relation::Eq, RealValue::fromInt(3), 1, TheoryId::NIA),
                     true, 1, SatLit{1, true});
    solver.assertLit(polyAtom(xPlusY, Relation::Eq, RealValue::fromInt(4), 2, TheoryId::NIA),
                     true, 1, SatLit{2, true});

    StubLemmaStorage db;
    auto r = solver.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("McsatSolver: backtrack then re-decide works") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(kernel.get(), nullptr);

    McsatSolver solver;
    solver.setEngine(std::move(engine), TheoryId::NRA);

    solver.assertLit(polyAtom(xp, Relation::Geq, RealValue::fromInt(0), 1),
                     true, 1, SatLit{1, true});
    StubLemmaStorage db;
    auto r1 = solver.check(db);
    CHECK(r1.kind == TheoryCheckResult::Kind::Consistent);

    // Backtrack discards the trail's theory decision. A fresh check
    // should still find x=0 again.
    solver.backtrackToLevel(0);
    auto r2 = solver.check(db);
    CHECK(r2.kind == TheoryCheckResult::Kind::Consistent);
}
