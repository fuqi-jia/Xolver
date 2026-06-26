// Tests for the Phase-6 single-variable NLSAT-style explain function.
//
// The implementation uses a kernel-only "simple bound intersection"
// approach (no AlgebraBackend dependency, so it works under the current
// TheoryFactory wiring which passes a null backend). Atoms of the form
//   v rel rhs  (where the polynomial is linear in v with no other vars)
// are intersected; if the intersection is empty the engine emits a
// theory-valid Conflict clause containing the SAT literals of the
// blocking atoms. Otherwise the feasible midpoint becomes a candidate.
//
// Soundness gate: every CHECK confirms either Conflict (with the right
// reasons) or Found (with a value that satisfies the constraint). The
// engine never reports the WRONG verdict.

#include "experimental/mcsat/MCSatTrail.h"
#include "theory/arith/logics/nra/engine/NlsatEngine.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomTypes.h"
#include "util/RealValue.h"

#include <doctest/doctest.h>
#include <memory>

using namespace xolver;
using namespace xolver::mcsat;

namespace {

TheoryAtomRecord polyAtom(PolyId p, Relation rel, mpq_class rhs,
                          SatVar sv) {
    TheoryAtomRecord rec;
    rec.satVar = sv;
    rec.theory = TheoryId::NRA;
    rec.isDynamic = false;
    rec.exprId = 0;
    PolynomialAtomPayload payload;
    payload.poly = p;
    payload.rel = rel;
    payload.rhs = RealValue::fromMpq(std::move(rhs));
    rec.payload = std::move(payload);
    return rec;
}

} // namespace

TEST_CASE("NlsatEngine explain: x >= 1 AND x <= -1 → Conflict (theory-valid clause)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    SatLit lit1{1, true}, lit2{2, true};
    engine.onAssertAtom(polyAtom(xp, Relation::Geq, mpq_class(1), 1), true, 1, lit1);
    engine.onAssertAtom(polyAtom(xp, Relation::Leq, mpq_class(-1), 2), true, 1, lit2);

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Conflict);
    REQUIRE(choice.blockingAtoms.size() == 2);

    auto clause = engine.explainConflict(trail, choice.blockingAtoms);
    REQUIRE(clause.size() == 2);
    // The clause carries the asserted (TRUE-on-trail) lits; the
    // framework negates them when emitting to SAT.
    CHECK((clause[0] == lit1 || clause[0] == lit2));
    CHECK((clause[1] == lit1 || clause[1] == lit2));
    CHECK(clause[0] != clause[1]);
}

TEST_CASE("NlsatEngine explain: x = 5 AND x > 10 → Conflict") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(5), 1),
                        true, 1, SatLit{1, true});
    engine.onAssertAtom(polyAtom(xp, Relation::Gt, mpq_class(10), 2),
                        true, 1, SatLit{2, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    CHECK(choice.kind == ValueChoice::Kind::Conflict);
}

TEST_CASE("NlsatEngine explain: x = 5 alone → Found(5) via simple-bound point") {
    // Without the simple-bound feasible-point augmentation, the rational
    // candidate set {0, ±1, ±2, ±1/2, ±3} doesn't contain 5; pickValue
    // would GiveUp. Phase 6 fixes this by feeding the bound's exact
    // value into the candidate list.
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(5), 1),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(5));
}

TEST_CASE("NlsatEngine explain: x >= 3 AND x <= 7 → Found via interval midpoint") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Geq, mpq_class(3), 1),
                        true, 1, SatLit{1, true});
    engine.onAssertAtom(polyAtom(xp, Relation::Leq, mpq_class(7), 2),
                        true, 1, SatLit{2, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    auto q = choice.value.tryAsRational();
    REQUIRE(q.has_value());
    // The chosen value must satisfy 3 ≤ v ≤ 7. (Midpoint 5 is what the
    // current heuristic produces; tolerate any value in range.)
    CHECK(*q >= mpq_class(3));
    CHECK(*q <= mpq_class(7));
}

TEST_CASE("NlsatEngine explain: strict bound x > 0 AND x < 0 → Conflict") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Gt, mpq_class(0), 1),
                        true, 1, SatLit{1, true});
    engine.onAssertAtom(polyAtom(xp, Relation::Lt, mpq_class(0), 2),
                        true, 1, SatLit{2, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    CHECK(choice.kind == ValueChoice::Kind::Conflict);
}

TEST_CASE("NlsatEngine explain: x = 5 AND x = 5 (consistent) → Found(5)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(5), 1),
                        true, 1, SatLit{1, true});
    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(5), 2),
                        true, 1, SatLit{2, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(5));
}

TEST_CASE("NlsatEngine explain: x = 5 AND x = 3 → Conflict") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xp = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(5), 1),
                        true, 1, SatLit{1, true});
    engine.onAssertAtom(polyAtom(xp, Relation::Eq, mpq_class(3), 2),
                        true, 1, SatLit{2, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    CHECK(choice.kind == ValueChoice::Kind::Conflict);
}
