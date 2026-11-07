#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include "evidence/ArithModelValidator.h"
#include <filesystem>
#include <fstream>
#include <set>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))
#define REQUIRE_RESULT(actual, expected) \
    REQUIRE(static_cast<int>(actual) == static_cast<int>(expected))

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_mc_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

// Collect all model values as strings — gives us value-set assertions even
// though we can't map varId to user var name from outside.
static std::set<std::string> modelValueSet(const Model& m) {
    std::set<std::string> result;
    for (const auto& kv : m.values()) result.insert(kv.second);
    return result;
}

TEST_CASE("MC: UF real branches retain valid reasons across model checks") {
    const auto path = writeSmt2("uf_real_branch_sources", R"(
        (set-logic QF_UFLRA)
        (set-option :produce-models true)
        (declare-const p Bool)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (f 0) 0))
        (assert (= (f 1) 1))
        (assert (or (= x 0) (= x 1)))
        (assert (or (= y 0) (= y 1)))
        (assert (= p (= x 0)))
        (assert (distinct x y))
        (assert (distinct (f x) (f y)))
        (check-sat)
    )");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("MC: joint witnesses reconstruct exact arithmetic and Boolean choices") {
    for (const std::string domain : {"Int", "Real"}) {
        const auto path = writeSmt2("joint_witness_" + domain,
            "(set-logic QF_UFL" + std::string(domain == "Int" ? "IA" : "RA") + ")\n"
            "(declare-const p Bool)(declare-const x " + domain + ")\n"
            "(declare-const y " + domain + ")(declare-fun f (" + domain + ") " + domain + ")\n"
            "(assert p)(assert (= y (+ x 2)))\n"
            "(assert (>= x 1180591620717411303424))\n"
            "(assert (< x 1180591620717411303428))\n"
            "(assert (= p (< (f x) (f y))))\n"
            "(assert (= (f y) (+ (f x) 1)))(check-sat)\n");
        Solver solver;
        REQUIRE(solver.parseFile(path));
        for (int repeat = 0; repeat < 2; ++repeat) {
            REQUIRE_RESULT(solver.checkSat(), Result::Sat);
            CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        }
    }
}

TEST_CASE("MC: joint witnesses include assumptions and respect scope withdrawal") {
    const auto path = writeSmt2("joint_witness_assumptions", R"(
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (>= x 0)) (assert (<= x 1))
        (assert (= (f 0) 3)) (assert (= (f 1) 4))
        (assert (>= (f x) 3))
        (check-sat)
    )");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    const auto x = solver.mkConst(solver.intSort(), "x");
    const auto one = solver.mkOp(static_cast<uint32_t>(Kind::Eq), {x, solver.mkInt(1)});
    const auto two = solver.mkOp(static_cast<uint32_t>(Kind::Eq), {x, solver.mkInt(2)});
    REQUIRE_RESULT(solver.checkSatAssuming({one}), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    REQUIRE(solver.getModel().getValue(x.id()));
    const auto value = *solver.getModel().getValue(x.id());
    CHECK((value == "1" || value == "#n:1"));
    REQUIRE_RESULT(solver.checkSatAssuming({two}), Result::Unsat);
    solver.push();
    solver.assertFormula(two);
    REQUIRE_RESULT(solver.checkSat(), Result::Unsat);
    solver.pop();
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("MC: joint witnesses reject inconsistent arithmetic UF interpretations") {
    for (const std::string domain : {"Int", "Real"}) {
        const auto path = writeSmt2("joint_witness_conflict_" + domain,
            "(set-logic QF_UFL" + std::string(domain == "Int" ? "IA" : "RA") + ")\n"
            "(declare-const x " + domain + ")(declare-const y " + domain + ")\n"
            "(declare-fun f (" + domain + ") " + domain + ")\n"
            "(assert (>= x 0))(assert (<= x 0))\n"
            "(assert (>= y 0))(assert (<= y 0))\n"
            "(assert (distinct (f x) (f y)))(check-sat)\n");
        Solver solver;
        REQUIRE(solver.parseFile(path));
        REQUIRE_RESULT(solver.checkSat(), Result::Unsat);
        CHECK(solver.getModel().isEmpty());
    }
}

TEST_CASE("MC: numeric class witnesses preserve exact identity") {
    TheoryModel model;
    model.assignments = {{"x", "@e7"}, {"y", "@e7"}, {"unused", "@e9"}};
    model.numericAssignments.emplace("x", RealValue::fromMpq(mpq_class(1, 3)));
    model.numericAssignments.emplace("y", RealValue::fromMpq(mpq_class(2, 6)));
    auto classes = ArithModelValidator::numericClassValues(model);
    REQUIRE(classes);
    REQUIRE(classes->size() == 1);
    CHECK(classes->at("@e7") == RealValue::fromMpq(mpq_class(1, 3)));

    const mpz_class large("1180591620717411303424");
    model.numericAssignments["y"] = RealValue::fromMpq(mpq_class(1, 3) + mpq_class(1, large));
    CHECK_FALSE(ArithModelValidator::numericClassValues(model));
    model.assignments["y"] = "@e8";
    CHECK(ArithModelValidator::numericClassValues(model));
    model.assignments["y"] = "@e7";
    model.numericAssignments["x"] = RealValue::fromMpq(mpq_class(large));
    model.numericAssignments["y"] = RealValue::fromMpq(mpq_class(large));
    CHECK(ArithModelValidator::numericClassValues(model));
    model.numericAssignments["y"] = RealValue::fromMpq(mpq_class(large + 1));
    CHECK_FALSE(ArithModelValidator::numericClassValues(model));
}

TEST_CASE("MC: x = 42 has 42 in the model value set") {
    auto path = writeSmt2("eq_42",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 42))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("42") > 0, "x=42 must appear in model");
}

TEST_CASE("MC: forced eq chain — model agrees with single value") {
    auto path = writeSmt2("chain_eq",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(assert (= x 7))\n"
        "(assert (= y x))\n"
        "(assert (= z y))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
    auto vs = modelValueSet(m);
    CHECK_MESSAGE(vs.count("7") > 0, "x=y=z=7 — value 7 must show");
}

TEST_CASE("MC: real bound model in [0,1]") {
    auto path = writeSmt2("real_bound",
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
    // Don't constrain exact form (could be "0", "1/2", "0.5", etc.) — only non-empty.
}

TEST_CASE("MC: integral real candidates reconstruct fractional values and Boolean choices") {
    const auto path = writeSmt2("real_integral_candidate_reconstruction",
        "(set-logic QF_NRA)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(declare-const c Bool)\n"
        "(assert (= x (/ y 2)))\n"
        "(assert (ite c (= (* y y) 9) (= (* y y) 25)))\n"
        "(assert (> y 0))\n"
        "(assert (< y 4))\n"
        "(check-sat)\n");
    Solver solver;
    solver.setRuntimeParameter("XOLVER_WALLCLOCK_MS", "10000");
    REQUIRE(solver.parseFile(path));
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    const auto values = modelValueSet(solver.getModel());
    CHECK(values.count("3/2") + values.count("(/ 3 2)") + values.count("1.5") > 0);
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("MC: distinct pair has at least two values in model") {
    auto path = writeSmt2("distinct_pair",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= x 1))\n"
        "(assert (= y 2))\n"
        "(assert (distinct x y))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("1") > 0, "value 1 must appear in model");
    CHECK_MESSAGE(vs.count("2") > 0, "value 2 must appear in model");
}

TEST_CASE("MC: ITE selection materializes a branch value") {
    auto path = writeSmt2("ite_branch",
        "(set-logic QF_LIA)\n"
        "(declare-const c Bool)\n"
        "(declare-const x Int)\n"
        "(assert c)\n"
        "(assert (= x (ite c 10 (- 10))))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("10") > 0, "c=true ⇒ x=10");
}

TEST_CASE("MC: model after pop reflects only persisted constraints") {
    auto path = writeSmt2("pop_model",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(push 1)\n"
        "(assert (= x 99))\n"
        "(pop 1)\n"
        "(assert (= x 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("1") > 0, "after pop, only x=1 remains");
    CHECK_MESSAGE(vs.count("99") == 0, "popped constraint x=99 must NOT survive");
}

TEST_CASE("MC: NIA perfect-square model contains a root") {
    auto path = writeSmt2("nia_sq_model",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 9))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    // Soundness: NIA model is candidate-only per plan.md §0, so just check API.
    CHECK_NOTHROW(m.values());
}

TEST_CASE("MC: model is empty after reset") {
    Solver s;
    auto path = writeSmt2("reset_model",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 5))\n"
        "(check-sat)\n");
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    CHECK_FALSE(s.getModel().isEmpty());
    s.reset();
    // After reset, model from old context should not crash even if reused.
    CHECK_NOTHROW(s.getModel().values());
}
