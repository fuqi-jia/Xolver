// Unit tests for the NIA-side MCSAT backend (NiaMcsatEngine).
//
// Mirrors the NRA test set but with integer-only semantics:
//   1. pickValue picks an INTEGER from the candidate set.
//   2. Non-integer trail values (RealValue::fromMpq(1,2)) → GiveUp.
//   3. validateModel rejects partial trails.
//   4. x^2 = 5 → GiveUp (no integer solution in candidate set).
//
// Soundness: the engine never returns Conflict in v0 (explanation function
// is still empty); a candidate that fails just leads to the next
// candidate, and exhaustion means GiveUp → framework returns Unknown.

#include "experimental/mcsat/MCSatTrail.h"
#include "theory/arith/nia/mcsat/NiaMcsatEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomTypes.h"
#include "util/RealValue.h"

#include <doctest/doctest.h>
#include <memory>

using namespace xolver;
using namespace xolver::mcsat;

namespace {

TheoryAtomRecord makePolyAtom(PolyId p, Relation rel, mpz_class rhs,
                              SatVar satVar = 1) {
    TheoryAtomRecord rec;
    rec.satVar = satVar;
    rec.theory = TheoryId::NIA;
    rec.isDynamic = false;
    rec.exprId = 0;
    PolynomialAtomPayload payload;
    payload.poly = p;
    payload.rel = rel;
    payload.rhs = RealValue::fromMpz(rhs);
    rec.payload = std::move(payload);
    return rec;
}

} // namespace

TEST_CASE("NiaMcsatEngine: pickNextVar returns x for x^2 - 4 = 0") {
    auto kernel = createPolynomialKernel();
    REQUIRE(kernel);

    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);
    PolyId xSq = kernel->pow(xPoly, 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());

    auto atom = makePolyAtom(xSqMinus4, Relation::Eq, mpz_class(0));
    engine.onAssertAtom(atom, /*value=*/true, /*level=*/1, SatLit{1, true});

    MCSatTrail trail;
    VarId next = engine.pickNextVar(trail);
    CHECK(next == x);
}

TEST_CASE("NiaMcsatEngine: pickValue returns 2 or -2 for x^2 = 4") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xSqMinus4, Relation::Eq, mpz_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value.isExactInteger());
    auto z = choice.value.tryAsRational();
    REQUIRE(z.has_value());
    CHECK((*z == mpq_class(2) || *z == mpq_class(-2)));
}

TEST_CASE("NiaMcsatEngine: pickValue returns 0 for x >= 0") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xPoly, Relation::Geq, mpz_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(0));
}

TEST_CASE("NiaMcsatEngine: pickValue honors a prior trail assignment") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xPlusY, Relation::Eq, mpz_class(3)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(1), 1));
    auto choice = engine.pickValue(y, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(2));
}

TEST_CASE("NiaMcsatEngine: validateModel accepts trail satisfying x^2 = 4 at x=2") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xSqMinus4, Relation::Eq, mpz_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(2), 1));

    TheorySolver::TheoryModel model;
    CHECK(engine.validateModel(trail, model));
    auto it = model.numericAssignments.find("x");
    REQUIRE(it != model.numericAssignments.end());
    CHECK(it->second == RealValue::fromInt(2));
}

TEST_CASE("NiaMcsatEngine: validateModel rejects trail violating x = 0") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xPoly, Relation::Eq, mpz_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(5), 1));

    TheorySolver::TheoryModel model;
    CHECK_FALSE(engine.validateModel(trail, model));
}

TEST_CASE("NiaMcsatEngine: pickValue gives up on x^2 = 5 (no integer root)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    PolyId xSqMinus5 = kernel->sub(xSq, kernel->mkConst(mpq_class(5)));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xSqMinus5, Relation::Eq, mpz_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    // No integer squares to 5. The integer-reinforcement path (square /
    // modular refuters, added with the relaxation-UNSAT step) now SOUNDLY
    // refutes this rather than merely giving up — pickValue returns a
    // Conflict (kind 1), which is strictly stronger than the old GiveUp.
    CHECK(choice.kind == ValueChoice::Kind::Conflict);
}

TEST_CASE("NiaMcsatEngine: pickValue gives up on non-integer trail value") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xPlusY, Relation::Eq, mpz_class(3)),
                        true, 1, SatLit{1, true});

    // Push a non-integer (1/2) onto the trail as if a previous theory
    // had decided x = 1/2. Sound NIA cannot proceed with such a value.
    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromMpq(mpq_class(1, 2)), 1));

    auto choice = engine.pickValue(y, trail);
    CHECK(choice.kind == ValueChoice::Kind::GiveUp);
}

TEST_CASE("NiaMcsatEngine: onBacktrack drops asserted atoms above target level") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());

    auto atomA = makePolyAtom(xPoly, Relation::Geq, mpz_class(0), 1);
    auto atomB = makePolyAtom(xPoly, Relation::Leq, mpz_class(0), 2);
    engine.onAssertAtom(atomA, true, /*level=*/1, SatLit{1, true});
    engine.onAssertAtom(atomB, true, /*level=*/2, SatLit{2, true});

    engine.onBacktrack(1);

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(0));
}

TEST_CASE("NiaMcsatEngine: pickValue finds 10 for x = 10") {
    // Confirms the candidate set reaches the wider end (10) for
    // constraints whose only integer answer is at the far edge.
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nia_mcsat::NiaMcsatEngine engine;
    engine.setKernel(kernel.get());
    engine.onAssertAtom(makePolyAtom(xPoly, Relation::Eq, mpz_class(10)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(10));
}
