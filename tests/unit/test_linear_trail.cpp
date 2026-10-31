#include <doctest/doctest.h>
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/linear/LinearTrailEntry.h"
#include <algorithm>
#include <type_traits>

using namespace xolver;

static_assert(std::is_trivially_copyable_v<LinearTrailEntry>);

namespace {
TheoryAtomRecord trailAtom(TheoryId theory, SatVar source, const std::string& name,
                          Relation relation, const mpq_class& rhs,
                          const mpq_class& coefficient = 1) {
    return {source, theory, false, ExprId(2000 + source),
        LinearAtomPayload{LinearFormKey{{{name, coefficient}}}, relation,
                          RealValue::fromMpq(rhs)}};
}

template<class Solver>
void checkIndependentSourceLifetime(TheoryId theory) {
    Solver solver;
    TheoryLemmaDatabase db;
    {
        auto atom = trailAtom(theory, 17, "owned-x", Relation::Eq, 3);
        solver.assertLit(atom, true, 1, {701, false});
        // No registry owns this record. Its form and all GMP objects can be
        // changed and destroyed immediately after the public assertion call.
        atom.payload = LinearAtomPayload{LinearFormKey{{{"other-y", 4}}},
                                        Relation::Eq, RealValue::fromMpq(999)};
    }
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.assertLit(trailAtom(theory, 18, "owned-x", Relation::Leq, 2), true, 2, {702, true});
    const auto result = solver.check(db);
    REQUIRE(result.kind == TheoryCheckResult::Kind::Conflict);
    CHECK(std::find(result.conflictOpt->clause.begin(), result.conflictOpt->clause.end(),
                    SatLit{701, false}) != result.conflictOpt->clause.end());
    CHECK(std::find(result.conflictOpt->clause.begin(), result.conflictOpt->clause.end(),
                    SatLit{702, true}) != result.conflictOpt->clause.end());
    solver.backtrackToLevel(1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.backtrackToLevel(0);
    solver.assertLit(trailAtom(theory, 19, "owned-x", Relation::Eq, 4), true, 0, {703, true});
    CHECK(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
}

template<class Solver>
void checkDistinctSourcesWithOneReason(TheoryId theory) {
    Solver solver;
    TheoryLemmaDatabase db;
    solver.assertLit(trailAtom(theory, 21, "source-x", Relation::Geq, 3), true, 1, {800, true});
    solver.assertLit(trailAtom(theory, 22, "source-x", Relation::Leq, 2), true, 1, {800, true});
    const auto result = solver.check(db);
    REQUIRE(result.kind == TheoryCheckResult::Kind::Conflict);
    REQUIRE(result.conflictOpt->clause.size() == 1);
    CHECK(result.conflictOpt->clause.front() == SatLit{800, true});
}
} // namespace

TEST_CASE("linear trail: canonical views outlive temporary forms and map growth") {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    int coordinate;
    {
        LinearFormKey temporary{{{"large-x", mpq_class("123456789012345678901234567890/7")}}};
        temporary.terms.front().second.canonicalize();
        coordinate = manager.getOrCreateAuxVar(simplex, temporary, mpq_class(5, 3));
        temporary.terms.clear();
    }
    const auto saved = manager.auxFormView(coordinate);
    REQUIRE(saved);
    for (int i = 0; i < 256; ++i) {
        const LinearFormKey form{{{"rehash-" + std::to_string(i), mpq_class(i + 1)}}};
        manager.getOrCreateAuxVar(simplex, form, mpq_class(i, 3));
    }
    const auto current = manager.auxFormView(coordinate);
    REQUIRE(current);
    CHECK(&saved->lhs == &current->lhs);
    CHECK(&saved->rhs == &current->rhs);
    REQUIRE(saved->lhs.terms.size() == 1);
    CHECK(saved->lhs.terms.front().first == "large-x");
    mpq_class expected("123456789012345678901234567890/7");
    expected.canonicalize();
    CHECK(saved->lhs.terms.front().second == expected);
    CHECK(saved->rhs == mpq_class(5, 3));
    CHECK_FALSE(manager.auxFormView(manager.findVarIndex("large-x")));
    LinearFormKey owned;
    mpq_class rhs;
    REQUIRE(manager.auxForm(coordinate, owned, rhs));
    owned.terms.clear();
    rhs = 0;
    CHECK(saved->lhs.terms.size() == 1);
    CHECK(saved->rhs == mpq_class(5, 3));
}

TEST_CASE("linear trail: LRA retains caller forms and signed reasons across rollback") {
    checkIndependentSourceLifetime<LraSolver>(TheoryId::LRA);
}

TEST_CASE("linear trail: LIA retains caller forms and signed reasons across rollback") {
    checkIndependentSourceLifetime<LiaSolver>(TheoryId::LIA);
}

TEST_CASE("linear trail: source identity is independent of the asserted reason") {
    checkDistinctSourcesWithOneReason<LraSolver>(TheoryId::LRA);
    checkDistinctSourcesWithOneReason<LiaSolver>(TheoryId::LIA);
}

TEST_CASE("linear trail: LIA snapshots restore replaced definitions and source metadata") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    solver.assertLit(trailAtom(TheoryId::LIA, 31, "snapshot-x", Relation::Eq, 3), true, 0, {901, true});
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.push();
    auto replacement = trailAtom(TheoryId::LIA, 31, "snapshot-y", Relation::Eq, 5);
    replacement.exprId = 5555;
    solver.assertLit(replacement, true, 0, {902, false});
    solver.assertLit(trailAtom(TheoryId::LIA, 32, "snapshot-x", Relation::Eq, 4), true, 0, {903, true});
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.pop();
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    const auto pin = solver.proveFixedValueByName("snapshot-x");
    REQUIRE(pin);
    CHECK(pin->first == 3);
    solver.assertLit(trailAtom(TheoryId::LIA, 33, "snapshot-x", Relation::Eq, 4), true, 0, {904, true});
    const auto conflict = solver.check(db);
    REQUIRE(conflict.kind == TheoryCheckResult::Kind::Conflict);
    CHECK(std::find(conflict.conflictOpt->clause.begin(), conflict.conflictOpt->clause.end(),
                    SatLit{901, true}) != conflict.conflictOpt->clause.end());
    CHECK(std::find(conflict.conflictOpt->clause.begin(), conflict.conflictOpt->clause.end(),
                    SatLit{902, false}) == conflict.conflictOpt->clause.end());
}

TEST_CASE("linear trail: cached integer strictness respects rational coefficients and rhs") {
    for (const auto& bounds : {std::pair{mpq_class(1, 2), mpq_class(1)},
                               std::pair{mpq_class(1), mpq_class(3, 2)}}) {
        LiaSolver solver;
        TheoryLemmaDatabase db;
        solver.assertLit(trailAtom(TheoryId::LIA, 41, "fraction-x", Relation::Lt,
                                   bounds.second, bounds.first), true, 1, {1001, true});
        solver.assertLit(trailAtom(TheoryId::LIA, 42, "fraction-x", Relation::Geq, 1), true, 1, {1002, true});
        solver.assertLit(trailAtom(TheoryId::LIA, 43, "temporary-y", Relation::Eq, 7), true, 2, {1003, true});
        REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
        solver.backtrackToLevel(1);
        CHECK(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    }
    LraSolver realSolver;
    TheoryLemmaDatabase db;
    realSolver.assertLit(trailAtom(TheoryId::LRA, 44, "real-x", Relation::Lt, 1), true, 1, {1004, true});
    realSolver.assertLit(trailAtom(TheoryId::LRA, 45, "real-x", Relation::Geq, mpq_class(1, 2)), true, 1, {1005, true});
    CHECK(realSolver.check(db).kind == TheoryCheckResult::Kind::Consistent);
}
