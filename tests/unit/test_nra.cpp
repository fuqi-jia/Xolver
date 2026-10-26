#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "applications/smt/qfnra/NraSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

TEST_CASE("NRA: box-sector explanations preserve a known rational witness") {
    const auto path = std::filesystem::path(__FILE__).parent_path().parent_path() /
                      "known_gaps/nra/box_sector_joint_reasons.smt2";
    Solver solver;
    solver.setRuntimeParameter("XOLVER_WALLCLOCK_MS", "10000");
    REQUIRE(solver.parseFile(path.string()));
    const auto result = solver.checkSat();
    INFO(solver.lastUnknownReason());
    CHECK((result != Result::Unsat));
    if (result == Result::Sat)
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

namespace {
struct NraStateFixture {
    NativeTerms terms;
    SharedTermRegistry shared;
    NraSolver solver{createPolynomialKernel()};
    TheoryLemmaDatabase lemmas;
    PolyId x;
    SharedTermId sx, zero, one;

    NraStateFixture() {
        terms.registerSort(0, SortKind::Real);
        shared.setNativeTerms(&terms);
        auto term = [&](Kind kind, const std::string& name) {
            const auto e = terms.add({kind, 0, {}, Payload(name)});
            return shared.getOrCreate(e, 0, name, false);
        };
        sx = term(Kind::Variable, "x");
        zero = term(Kind::ConstReal, "0");
        one = term(Kind::ConstReal, "1");
        solver.setNativeTerms(&terms);
        solver.setSharedTermRegistry(&shared);
        x = solver.kernel()->mkVar(solver.kernel()->getOrCreateVar("x"));
    }

    void atom(PolyId poly, Relation rel, int rhs, SatVar reason, int level = 0,
              bool value = true) {
        TheoryAtomRecord a{reason, TheoryId::NRA, false, NullExpr,
            PolynomialAtomPayload{poly, rel, RealValue::fromMpq(mpq_class(rhs))}};
        solver.assertLit(a, value, level,
                         value ? SatLit::positive(reason) : SatLit::negative(reason));
    }
    TheoryCheckResult check(TheoryEffort effort = TheoryEffort::Full) {
        return solver.check(lemmas, effort);
    }
    void modelIs(int value) {
        const auto model = solver.getModel();
        REQUIRE(model.has_value());
        REQUIRE(model->numericAssignments.count("x") == 1);
        CHECK(model->numericAssignments.at("x").tryAsRational() == mpq_class(value));
    }
};
}

TEST_CASE("NRA state: cached witnesses obey new interface constraints") {
    NraStateFixture f;
    f.atom(f.x, Relation::Eq, 0, 1);
    REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
    f.modelIs(0);
    SUBCASE("equality") {
        REQUIRE(f.solver.assertInterfaceEquality(f.sx, f.one, SatLit::positive(2), 1).kind
                == TheoryCheckResult::Kind::Consistent);
    }
    SUBCASE("disequality") {
        REQUIRE(f.solver.assertInterfaceDisequality(f.sx, f.zero, SatLit::positive(2), 1).kind
                == TheoryCheckResult::Kind::Consistent);
    }
    CHECK_FALSE(f.solver.getModel().has_value());
    CHECK(f.check().kind == TheoryCheckResult::Kind::Conflict);
    f.solver.backtrackToLevel(0);
    REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
    f.modelIs(0);
}

TEST_CASE("NRA state: polynomial RHS reaches the combination backend") {
    NraStateFixture f;
    const auto square = f.solver.kernel()->mul(f.x, f.x);
    SUBCASE("positive equality has a nonzero RHS") {
        f.atom(square, Relation::Eq, 2, 1);
        REQUIRE(f.solver.assertInterfaceEquality(f.sx, f.zero, SatLit::positive(2), 0).kind
                == TheoryCheckResult::Kind::Consistent);
        CHECK(f.check().kind == TheoryCheckResult::Kind::Conflict);
    }
    SUBCASE("negated equality preserves the RHS") {
        f.atom(square, Relation::Eq, 2, 1, 0, false);
        REQUIRE(f.solver.assertInterfaceEquality(f.sx, f.zero, SatLit::positive(2), 0).kind
                == TheoryCheckResult::Kind::Consistent);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.modelIs(0);
    }
}

TEST_CASE("NRA state: pop restores interface constraints and decision trails") {
    NraStateFixture f;
    SUBCASE("scope removes interface equality") {
        f.solver.push();
        f.solver.assertInterfaceEquality(f.sx, f.zero, SatLit::positive(1), 0);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.modelIs(0);
        f.solver.pop(1);
        f.atom(f.x, Relation::Eq, 1, 2);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.modelIs(1);
    }
    SUBCASE("scope removes interface disequality") {
        f.solver.push();
        f.solver.assertInterfaceDisequality(f.sx, f.zero, SatLit::positive(1), 0);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.solver.pop(1);
        f.atom(f.x, Relation::Eq, 0, 2);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.modelIs(0);
    }
    SUBCASE("remaining outer decisions can still backtrack") {
        f.atom(f.x, Relation::Eq, 0, 1, 1);
        f.solver.push();
        f.atom(f.x, Relation::Leq, 2, 2, 2);
        f.solver.pop(1);
        f.solver.backtrackToLevel(0);
        f.atom(f.x, Relation::Eq, 1, 3, 1);
        REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
        f.modelIs(1);
    }
}

TEST_CASE("NRA state: model search is scheduled after partial propagation") {
    NraStateFixture f;
    f.atom(f.x, Relation::Eq, 0, 1, 1);
    REQUIRE(f.check(TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
    CHECK_FALSE(f.solver.getModel().has_value());
    REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
    f.modelIs(0);
    f.solver.backtrackToLevel(0);
    f.atom(f.x, Relation::Eq, 1, 2, 1);
    REQUIRE(f.check().kind == TheoryCheckResult::Kind::Consistent);
    f.modelIs(1);
    f.solver.backtrackToLevel(1);  // SAT callback may report a no-op backtrack.
    f.modelIs(1);
}

TEST_CASE("NRA state: unsupported payload cannot erase an existing constraint") {
    NraStateFixture f;
    f.atom(f.x, Relation::Eq, 0, 1);
    f.solver.push();
    TheoryAtomRecord unsupported{2, TheoryId::NRA, false, NullExpr, LinearAtomPayload{}};
    f.solver.assertLit(unsupported, true, 1, SatLit::positive(2));
    CHECK(f.check().kind == TheoryCheckResult::Kind::Unknown);
    f.solver.pop(1);
    f.atom(f.x, Relation::Eq, 1, 3);
    CHECK(f.check().kind == TheoryCheckResult::Kind::Conflict);
}

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_nra.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("NRA: trivial constant unsat (= 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (= 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NRA: trivial constant sat (> 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (> 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NRA: non-constant unsat (= (+ (* x x) 1) 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(declare-const x Real)\n"
        "(assert (= (+ (* x x) 1) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NRA: false literal negation (not (> 1 0)) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (not (> 1 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NRA: distinct constant unsat (distinct 1 1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (distinct 1 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NRA: eq negation constant unsat (not (= 1 1))") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (not (= 1 1)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NRA: non-integer rational constant returns Unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NRA)\n"
        "(assert (= (/ 1 2) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NRA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}
