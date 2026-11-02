#include <doctest/doctest.h>
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"

using namespace xolver;

namespace {
template<class Engine>
void checkWithdrawnInterface(TheoryId theory, bool disequality, bool applied) {
    INFO("theory=", static_cast<int>(theory), " disequality=", disequality,
         " previously checked=", applied);
    NativeTerms terms;
    terms.registerSort(0, theory == TheoryId::LRA ? SortKind::Real : SortKind::Int);
    const auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("reset-x"))});
    const auto one = terms.add({theory == TheoryId::LRA ? Kind::ConstReal : Kind::ConstInt,
                                0, {}, Payload(std::string("1"))});
    SharedTermRegistry shared;
    shared.setNativeTerms(&terms);
    const auto sx = shared.getOrCreate(x, 0, "reset-x", false);
    const auto sone = shared.getOrCreate(one, 0, "1", false);
    Engine engine;
    engine.setNativeTerms(&terms);
    engine.setSharedTermRegistry(&shared);
    const auto previous = disequality
        ? engine.assertInterfaceDisequality(sx, sone, {1, true}, 0)
        : engine.assertInterfaceEquality(sx, sone, {1, true}, 0);
    REQUIRE(previous.kind == TheoryCheckResult::Kind::Consistent);
    TheoryLemmaDatabase oldLemmas;
    if (applied)
        REQUIRE(engine.check(oldLemmas).kind == TheoryCheckResult::Kind::Consistent);

    engine.reset();
    const int expected = disequality ? 1 : 0;
    const LinearFormKey form{{{"reset-x", mpq_class(1)}}};
    const TheoryAtomRecord current{2, theory, false, NullExpr,
        LinearAtomPayload{form, Relation::Eq, RealValue::fromInt(expected)}};
    engine.assertLit(current, true, 0, {2, true});
    TheoryLemmaDatabase newLemmas;
    REQUIRE(engine.check(newLemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = engine.getModel();
    REQUIRE(model);
    REQUIRE(model->numericAssignments.count("reset-x") == 1);
    CHECK(model->numericAssignments.at("reset-x").tryAsRational() == mpq_class(expected));

    // Reuse the same source after another reset: no withdrawn interface fact,
    // bound, or previous model may constrain the next assertion context.
    engine.reset();
    auto next = current;
    next.payload = LinearAtomPayload{form, Relation::Eq, RealValue::fromInt(2)};
    engine.assertLit(next, true, 0, {2, true});
    REQUIRE(engine.check(newLemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto nextModel = engine.getModel();
    REQUIRE(nextModel);
    CHECK(nextModel->numericAssignments.at("reset-x").tryAsRational() == mpq_class(2));
}
} // namespace

TEST_CASE("Arithmetic reset: withdraw old interface equalities before checking a new context") {
    for (bool applied : {false, true}) {
        checkWithdrawnInterface<LraSolver>(TheoryId::LRA, false, applied);
        checkWithdrawnInterface<LiaSolver>(TheoryId::LIA, false, applied);
    }
}

TEST_CASE("Arithmetic reset: withdraw old interface disequalities before checking a new context") {
    for (bool applied : {false, true}) {
        checkWithdrawnInterface<LraSolver>(TheoryId::LRA, true, applied);
        checkWithdrawnInterface<LiaSolver>(TheoryId::LIA, true, applied);
    }
}

TEST_CASE("LRA replacement withdraws old bounds and cached conflicts") {
    LraSolver engine;
    TheoryLemmaDatabase lemmas;
    const LinearFormKey x{{{"replacement-x", 1}}};
    TheoryAtomRecord source{1, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Geq, RealValue::fromInt(2)}};
    const TheoryAtomRecord ceiling{2, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Leq, RealValue::fromInt(1)}};
    engine.assertLit(source, true, 0, {1, true});
    engine.assertLit(ceiling, true, 0, {2, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);

    // Changing the RHS creates a different auxiliary coordinate. The old
    // bound and the conflict it caused must both disappear.
    source.payload = LinearAtomPayload{x, Relation::Geq, RealValue::fromInt(0)};
    engine.assertLit(source, true, 0, {1, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = engine.getModel();
    REQUIRE(model);
    const auto value = model->numericAssignments.at("replacement-x").tryAsRational();
    REQUIRE(value);
    CHECK(*value >= 0);
    CHECK(*value <= 1);

    // A relation-only replacement reuses the same auxiliary coordinate.
    source.payload = LinearAtomPayload{x, Relation::Gt, RealValue::fromInt(1)};
    engine.assertLit(source, true, 0, {1, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    std::get<LinearAtomPayload>(source.payload).rel = Relation::Leq;
    engine.assertLit(source, true, 0, {1, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto relaxed = engine.getModel();
    REQUIRE(relaxed);
    CHECK(relaxed->numericAssignments.at("replacement-x").tryAsRational() <= mpq_class(1));
}

TEST_CASE("LRA scopes restore sources after replacement conflicts and root replay") {
    LraSolver engine;
    TheoryLemmaDatabase lemmas;
    const LinearFormKey x{{{"scoped-x", 1}}};
    TheoryAtomRecord source{1, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Eq, RealValue::fromInt(0)}};
    const auto checkValue = [&](int expected) {
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        const auto model = engine.getModel();
        REQUIRE(model);
        CHECK(model->numericAssignments.at("scoped-x").tryAsRational() == mpq_class(expected));
    };
    engine.assertLit(source, true, 0, {1, true});
    checkValue(0);
    engine.push();
    std::get<LinearAtomPayload>(source.payload).rhs = RealValue::fromInt(1);
    engine.assertLit(source, true, 0, {1, true});
    checkValue(1);
    engine.push();
    const TheoryAtomRecord excluded{2, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Leq, RealValue::fromInt(1)}};
    engine.assertLit(excluded, false, 1, {2, false});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    engine.pop(1);
    checkValue(1);

    // Root restarts clear the live source base, but must preserve API scopes.
    engine.backtrackToLevel(0);
    std::get<LinearAtomPayload>(source.payload).rhs = RealValue::fromInt(2);
    engine.restoreRootLiteral(source, true, {1, true});
    checkValue(2);
    engine.pop(1);
    checkValue(0);
    engine.pop(0);
    checkValue(0);

    engine.push();
    engine.assertLit(excluded, false, 1, {2, false});
    engine.push();
    engine.pop(2);
    checkValue(0);
}

TEST_CASE("LRA backtracking withdraws interior sources after level replacement") {
    LraSolver engine;
    TheoryLemmaDatabase lemmas;
    const LinearFormKey x{{{"interior-x", 1}}};
    const TheoryAtomRecord lower{1, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Geq, RealValue::fromInt(2)}};
    const TheoryAtomRecord upper{2, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Leq, RealValue::fromInt(1)}};
    engine.assertLit(lower, true, 1, {1, true});
    engine.assertLit(upper, true, 1, {2, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    engine.assertLit(lower, true, 2, {1, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    engine.backtrackToLevel(1);
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = engine.getModel();
    REQUIRE(model);
    CHECK(model->numericAssignments.at("interior-x").tryAsRational() <= mpq_class(1));
}
