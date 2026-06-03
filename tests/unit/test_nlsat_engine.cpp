// Unit tests for the NRA-side MCSAT backend (NlsatEngine).
//
// These cover the Phase-2 deliverable:
//   1. pickNextVar — returns a VarId referenced by an asserted atom.
//   2. pickValue   — returns a feasible rational from the candidate set,
//                    rejecting candidates that violate any fully-evaluable
//                    asserted atom.
//   3. validateModel — true only when every asserted atom is satisfied by
//                     the trail's value assignment.
//
// Soundness is the gate: a value returned by pickValue must satisfy every
// atom that is evaluable to a constant under the current trail.

#include "experimental/mcsat/MCSatTrail.h"
#include "theory/arith/nra/nlsat/NlsatEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomTypes.h"
#include "util/RealValue.h"

#include <doctest/doctest.h>
#include <memory>

using namespace xolver;
using namespace xolver::mcsat;

namespace {

// Build a TheoryAtomRecord wrapping (poly rel rhs) so we can hand it to
// the engine without the full SAT-side machinery.
TheoryAtomRecord makePolyAtom(PolyId p, Relation rel, mpq_class rhs,
                              SatVar satVar = 1) {
    TheoryAtomRecord rec;
    rec.satVar = satVar;
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

TEST_CASE("NlsatEngine: pickNextVar returns x for x^2 - 4 = 0") {
    auto kernel = createPolynomialKernel();
    REQUIRE(kernel);

    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);
    PolyId xSq = kernel->pow(xPoly, 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), /*backend=*/nullptr);

    auto atom = makePolyAtom(xSqMinus4, Relation::Eq, mpq_class(0));
    engine.onAssertAtom(atom, /*value=*/true, /*level=*/1, SatLit{1, true});

    MCSatTrail trail;
    VarId next = engine.pickNextVar(trail);
    CHECK(next == x);
}

TEST_CASE("NlsatEngine: pickValue returns 2 or -2 for x^2 = 4") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xSqMinus4, Relation::Eq, mpq_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    auto v = choice.value.tryAsRational();
    REQUIRE(v.has_value());
    // The candidate set walks 0, 1, -1, 2, -2, ... — the first that
    // satisfies x^2 = 4 is x = 2.
    CHECK((*v == mpq_class(2) || *v == mpq_class(-2)));
}

TEST_CASE("NlsatEngine: pickValue returns 0 for x >= 0 (candidate 0 first)") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xPoly, Relation::Geq, mpq_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    // After mgc-B the positive-bias prefers 1 over 0 for `x ≥ 0`. Both
    // satisfy the constraint — accept either.
    auto q = choice.value.tryAsRational();
    REQUIRE(q.has_value());
    CHECK(*q >= mpq_class(0));
}

TEST_CASE("NlsatEngine: validateModel accepts trail satisfying x^2 = 4 at x=2") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    PolyId xSqMinus4 = kernel->sub(xSq, kernel->mkConst(mpq_class(4)));

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xSqMinus4, Relation::Eq, mpq_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(2), 1));

    TheorySolver::TheoryModel model;
    CHECK(engine.validateModel(trail, model));
    // The model channel should carry x = 2.
    auto it = model.numericAssignments.find("x");
    REQUIRE(it != model.numericAssignments.end());
    CHECK(it->second == RealValue::fromInt(2));
}

TEST_CASE("NlsatEngine: validateModel rejects trail violating x = 0") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xPoly, Relation::Eq, mpq_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(5), 1));

    TheorySolver::TheoryModel model;
    CHECK_FALSE(engine.validateModel(trail, model));
}

TEST_CASE("NlsatEngine: pickValue gives up when no rational candidate works") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xSq = kernel->pow(kernel->mkVar(x), 2);
    // x^2 = 5 has no rational solution; the candidate set 0,±1,±2,±1/2,±3
    // contains none whose square equals 5, so pickValue must give up.
    PolyId xSqMinus5 = kernel->sub(xSq, kernel->mkConst(mpq_class(5)));

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xSqMinus5, Relation::Eq, mpq_class(0)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    CHECK(choice.kind == ValueChoice::Kind::GiveUp);
}

TEST_CASE("NlsatEngine: onBacktrack drops asserted atoms above target level") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    auto atomA = makePolyAtom(xPoly, Relation::Geq, mpq_class(0), 1);
    auto atomB = makePolyAtom(xPoly, Relation::Leq, mpq_class(0), 2);
    engine.onAssertAtom(atomA, true, /*level=*/1, SatLit{1, true});
    engine.onAssertAtom(atomB, true, /*level=*/2, SatLit{2, true});

    engine.onBacktrack(1);

    // After backtrack to level 1, only atomA remains. pickValue should
    // accept any value with x >= 0. (mgc-B sign-bias prefers 1.)
    MCSatTrail trail;
    auto choice = engine.pickValue(x, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    auto q = choice.value.tryAsRational();
    REQUIRE(q.has_value());
    CHECK(*q >= mpq_class(0));
}

TEST_CASE("NlsatEngine: pickValue honors a prior trail assignment of another var") {
    auto kernel = createPolynomialKernel();
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    // Constraint: x + y = 3.
    PolyId xPlusY = kernel->add(kernel->mkVar(x), kernel->mkVar(y));

    nlsat::NlsatEngine engine;
    engine.setAlgebra(kernel.get(), nullptr);

    engine.onAssertAtom(makePolyAtom(xPlusY, Relation::Eq, mpq_class(3)),
                        true, 1, SatLit{1, true});

    MCSatTrail trail;
    // First assign x = 1 → then a feasible y must be 2.
    REQUIRE(trail.pushTheoryDecision(x, RealValue::fromInt(1), 1));
    auto choice = engine.pickValue(y, trail);
    REQUIRE(choice.kind == ValueChoice::Kind::Found);
    CHECK(choice.value == RealValue::fromInt(2));
}
