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
