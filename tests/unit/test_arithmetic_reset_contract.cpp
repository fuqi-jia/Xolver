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

TEST_CASE("Arithmetic admission: exact replays retain payload replacement and scope semantics") {
    const auto check = []<class Engine>(TheoryId theory) {
        Engine engine;
        TheoryLemmaDatabase lemmas;
        mpq_class coefficient((mpz_class(1) << 181) + 7, (mpz_class(1) << 139) + 3);
        coefficient.canonicalize();
        const LinearFormKey x{{{"admission-x", coefficient}}};
        const LinearFormKey y{{{"admission-y", coefficient}}};
        TheoryAtomRecord source{1, theory, false, NullExpr,
            LinearAtomPayload{x, Relation::Eq, RealValue::fromInt(0)}};
        const TheoryAtomRecord anchor{2, theory, false, NullExpr,
            LinearAtomPayload{x, Relation::Eq, RealValue::fromInt(0)}};
        const auto consistent = [&] {
            REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        };
        const auto value = [&](const std::string& name) {
            const auto model = engine.getModel();
            REQUIRE(model);
            REQUIRE(model->numericAssignments.contains(name));
            const auto number = model->numericAssignments.at(name).tryAsRational();
            REQUIRE(number);
            return *number;
        };
        engine.assertLit(anchor, true, 0, {2, true});
        for (int repeat = 0; repeat < 4; ++repeat) engine.assertLit(source, true, 0, {1, true});
        consistent();
        engine.assertLit(source, true, 0, {1, true});
        consistent();
        CHECK(value("admission-x") == 0);

        // Reusing SAT and expression IDs does not identify a changed payload.
        source.payload = LinearAtomPayload{x, Relation::Eq, RealValue::fromMpq(coefficient)};
        engine.assertLit(source, true, 0, {1, true});
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
        engine.assertLit(source, true, 0, {1, true});
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
        source.payload = LinearAtomPayload{y, Relation::Eq, RealValue::fromMpq(coefficient)};
        engine.assertLit(source, true, 0, {1, true});
        consistent();
        CHECK(value("admission-x") == 0);
        CHECK(value("admission-y") == 1);

        // A level replacement must still withdraw the former root source.
        engine.assertLit(source, true, 2, {1, true});
        consistent();
        engine.backtrackToLevel(1);
        const TheoryAtomRecord next{3, theory, false, NullExpr,
            LinearAtomPayload{y, Relation::Eq, RealValue::fromMpq(2 * coefficient)}};
        engine.assertLit(next, true, 1, {3, true});
        consistent();
        CHECK(value("admission-y") == 2);

        engine.reset();
        engine.assertLit(anchor, true, 0, {2, true});
        engine.assertLit(source, true, 0, {1, true});
        consistent();
        engine.push();
        std::get<LinearAtomPayload>(source.payload).rel = Relation::Leq;
        engine.assertLit(source, false, 1, {1, false});
        consistent();
        CHECK(value("admission-y") > 1);
        engine.pop(1);
        consistent();
        CHECK(value("admission-y") == 1);
    };
    check.template operator()<LraSolver>(TheoryId::LRA);
    check.template operator()<LiaSolver>(TheoryId::LIA);
}

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

TEST_CASE("LRA backtracking orders ordinary and interface bound sources together") {
    for (bool checkBeforeInterface : {false, true}) {
        CAPTURE(checkBeforeInterface);
        NativeTerms terms;
        terms.registerSort(0, SortKind::Real);
        const auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("ordered-y"))});
        const auto zero = terms.add({Kind::ConstReal, 0, {}, Payload(std::string("0"))});
        SharedTermRegistry shared;
        shared.setNativeTerms(&terms);
        const auto sy = shared.getOrCreate(y, 0, "ordered-y", false);
        const auto szero = shared.getOrCreate(zero, 0, "0", false);
        LraSolver engine;
        engine.setNativeTerms(&terms);
        engine.setSharedTermRegistry(&shared);
        TheoryLemmaDatabase lemmas;
        const LinearFormKey x{{{"ordered-x", 1}}};
        const TheoryAtomRecord lower{1, TheoryId::LRA, false, NullExpr,
            LinearAtomPayload{x, Relation::Geq, RealValue::fromInt(2)}};
        const TheoryAtomRecord upper{3, TheoryId::LRA, false, NullExpr,
            LinearAtomPayload{x, Relation::Leq, RealValue::fromInt(1)}};
        engine.assertLit(lower, true, 3, {1, true});
        if (checkBeforeInterface)
            REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        REQUIRE(engine.assertInterfaceEquality(sy, szero, {2, true}, 0).kind ==
                TheoryCheckResult::Kind::Consistent);
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);

        // A late, weaker bound must survive withdrawal of the stronger child.
        const TheoryAtomRecord retained{4, TheoryId::LRA, false, NullExpr,
            LinearAtomPayload{x, Relation::Geq, RealValue::fromInt(0)}};
        engine.assertLit(retained, true, 1, {4, true});
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);

        // The root interface equality must not hide the earlier high-level
        // ordinary bound from the simplex's suffix rollback.
        engine.backtrackToLevel(1);
        engine.assertLit(upper, true, 1, {3, true});
        REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        const auto model = engine.getModel();
        REQUIRE(model);
        CHECK(model->numericAssignments.at("ordered-x").tryAsRational() >= mpq_class(0));
        CHECK(model->numericAssignments.at("ordered-x").tryAsRational() <= mpq_class(1));
        CHECK(model->numericAssignments.at("ordered-y").tryAsRational() == mpq_class(0));
    }
}

TEST_CASE("LRA interface rollback retains unapplied lower-level sources") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    const auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("pending-y"))});
    const auto zero = terms.add({Kind::ConstReal, 0, {}, Payload(std::string("0"))});
    const auto one = terms.add({Kind::ConstReal, 0, {}, Payload(std::string("1"))});
    SharedTermRegistry shared;
    shared.setNativeTerms(&terms);
    const auto sy = shared.getOrCreate(y, 0, "pending-y", false);
    const auto szero = shared.getOrCreate(zero, 0, "0", false);
    const auto sone = shared.getOrCreate(one, 0, "1", false);
    LraSolver engine;
    engine.setNativeTerms(&terms);
    engine.setSharedTermRegistry(&shared);
    TheoryLemmaDatabase lemmas;
    REQUIRE(engine.assertInterfaceEquality(sy, szero, {1, true}, 3).kind ==
            TheoryCheckResult::Kind::Consistent);
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    REQUIRE(engine.assertInterfaceEquality(sy, sone, {2, true}, 1).kind ==
            TheoryCheckResult::Kind::Consistent);
    engine.backtrackToLevel(1);
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = engine.getModel();
    REQUIRE(model);
    CHECK(model->numericAssignments.at("pending-y").tryAsRational() == mpq_class(1));
}

TEST_CASE("LRA interrupted admission retains successful prefixes and rejected sources") {
    LraSolver engine;
    TheoryLemmaDatabase lemmas;
    const LinearFormKey x{{{"prefix-x", 1}}};
    const TheoryAtomRecord upper{1, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Leq, RealValue::fromInt(0)}};
    const TheoryAtomRecord lower{4, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{x, Relation::Gt, RealValue::fromInt(0)}};
    engine.assertLit(upper, true, 0, {1, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);

    for (int level : {1, 2}) {
        const std::string name = level == 1 ? "prefix-y" : "prefix-z";
        const TheoryAtomRecord retained{static_cast<SatVar>(level + 1), TheoryId::LRA,
            false, NullExpr, LinearAtomPayload{LinearFormKey{{{name, 1}}},
                Relation::Geq, RealValue::fromInt(1)}};
        engine.assertLit(retained, true, level, {retained.satVar, true});
    }
    engine.assertLit(lower, true, 3, {4, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    engine.backtrackToLevel(2);
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = engine.getModel();
    REQUIRE(model);
    CHECK(model->numericAssignments.at("prefix-x").tryAsRational() <= mpq_class(0));
    CHECK(model->numericAssignments.at("prefix-y").tryAsRational() >= mpq_class(1));
    CHECK(model->numericAssignments.at("prefix-z").tryAsRational() >= mpq_class(1));

    engine.assertLit(lower, true, 2, {4, true});
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    // A no-op withdrawal still retains the rejected source. The simplex's
    // cleared conflict status must not turn that source context into SAT.
    engine.backtrackToLevel(2);
    REQUIRE(engine.check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
}
