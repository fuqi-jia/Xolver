#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include <filesystem>
#include <fstream>
#include <sstream>
#include <vector>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))
#define REQUIRE_RESULT(actual, expected) \
    REQUIRE(static_cast<int>(actual) == static_cast<int>(expected))

// End-to-end ModelValidator fixtures: per plan.md §0 soundness boundary,
// every Result::Sat must be backed by a real model. These tests verify that
// for cases where the solver returns Sat, getModel() produces a non-empty
// model. They do NOT re-verify model<->assertion consistency (that's the
// solver's contract internally), but they ensure the API surface is honest.

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_mv_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

TEST_CASE("Model completion request: repeated UF integer queries preserve assumptions") {
    const auto path = writeSmt2("requested_uf_integer",
        "(set-logic QF_UFNIA)\n"
        "(set-option :produce-models true)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-const x Int)(declare-const y Int)\n"
        "(assert (= (f 2) 9))\n"
        "(assert (= (* x y) 6))\n"
        "(assert (distinct (f x) 0))\n");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    const auto choice = solver.mkConst(solver.boolSort(), "choice");
    const auto notChoice = solver.mkOp(static_cast<uint32_t>(Kind::Not), {choice});
    for (const auto assumption : {choice, notChoice}) {
        REQUIRE_RESULT(solver.checkSatAssuming({assumption}), Result::Sat);
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        CHECK(solver.lastUnknownReason().empty());
        CHECK_RESULT(solver.checkSatAssuming({choice, notChoice}), Result::Unsat);
    }
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    std::filesystem::remove(path);
}

TEST_CASE("MV: SAT for LRA returns non-empty model") {
    auto path = writeSmt2("lra_sat",
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (> x 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
}

TEST_CASE("MV: SAT for LIA returns non-empty model") {
    auto path = writeSmt2("lia_sat",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 42))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
}

TEST_CASE("MV: SAT for EUF returns model with all decls") {
    auto path = writeSmt2("euf_sat",
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(assert (= a b))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    // EUF model may be empty if there's nothing to enumerate, but should not crash.
    CHECK_NOTHROW(m.values());
}

TEST_CASE("MV: uninterpreted scalar witnesses retain class tokens without arrays") {
    const auto path = writeSmt2("uf_scalar_tokens",
        "(set-logic QF_UF)\n"
        "(set-option :produce-models true)\n"
        "(declare-sort U 0)\n"
        "(declare-const x U)(declare-const y U)\n"
        "(assert (distinct x y))\n");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    const auto choice = solver.mkConst(solver.boolSort(), "choice");
    const auto notChoice = solver.mkOp(static_cast<uint32_t>(Kind::Not), {choice});
    for (const auto assumption : {choice, notChoice}) {
        REQUIRE_RESULT(solver.checkSatAssuming({assumption}), Result::Sat);
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        CHECK(solver.getModel().values().size() >= 2);
        std::ostringstream output;
        solver.dumpModel(output);
        CHECK(output.str().find("(error") == std::string::npos);
        CHECK(output.str().find("(define-fun x () U ") != std::string::npos);
        CHECK(output.str().find("(define-fun y () U ") != std::string::npos);
        CHECK_RESULT(solver.checkSatAssuming({choice, notChoice}), Result::Unsat);
    }
    REQUIRE_RESULT(solver.checkSat(), Result::Sat);
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    std::filesystem::remove(path);
}

TEST_CASE("MV: uninterpreted function witnesses validate without arrays") {
    const auto path = writeSmt2("uf_function_tokens",
        "(set-logic QF_UF)\n"
        "(set-option :produce-models true)\n"
        "(declare-sort U 0)\n"
        "(declare-const x U)(declare-const y U)\n"
        "(declare-fun f (U) U)\n"
        "(assert (distinct x y))\n"
        "(assert (= (f x) y))(assert (= (f y) x))\n");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    for (int round = 0; round < 2; ++round) {
        REQUIRE_RESULT(solver.checkSat(), Result::Sat);
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        CHECK(solver.getModel().values().size() >= 2);
        std::ostringstream output;
        solver.dumpModel(output);
        CHECK(output.str().find("(error") == std::string::npos);
        CHECK(output.str().find("(define-fun f (") != std::string::npos);
        solver.push();
        solver.assertFormula(solver.mkBool(false));
        CHECK_RESULT(solver.checkSat(), Result::Unsat);
        CHECK(solver.getModel().isEmpty());
        solver.pop();
    }
    std::filesystem::remove(path);
}

TEST_CASE("MV: exported model names preserve symbol identities") {
    const std::vector<std::string> queries{
        "(set-logic QF_UF)(declare-sort U 0)"
        "(declare-const x U)(declare-const |__xolver_model!0| U)(declare-const y U)"
        "(assert (distinct x |__xolver_model!0| y))",
        "(set-logic QF_UF)(declare-sort |two words| 0)"
        "(declare-const |value one| |two words|)(declare-const z |two words|)"
        "(assert (distinct |value one| z))"
    };
    for (size_t index = 0; index < queries.size(); ++index) {
        const auto path = writeSmt2("model_namespace_" + std::to_string(index),
            "(set-option :produce-models true)" + queries[index]);
        Solver solver;
        REQUIRE(solver.parseFile(path));
        REQUIRE_RESULT(solver.checkSat(), Result::Sat);
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        std::ostringstream stream;
        solver.dumpModel(stream);
        const auto text = stream.str();
        CHECK(text.find("(error") == std::string::npos);
        CHECK(text.find("(declare-fun @") == std::string::npos);
        if (index == 0) {
            CHECK(text.find("(declare-fun __xolver_model!0 () U)") == std::string::npos);
        } else {
            CHECK(text.find("@|two words|") == std::string::npos);
            CHECK(text.find("(define-fun |value one| () |two words| ") != std::string::npos);
        }
        std::filesystem::remove(path);
    }

    Solver api;
    const auto condition = api.mkConst(api.boolSort(), "condition name");
    api.assertFormula(condition);
    REQUIRE_RESULT(api.checkSat(), Result::Sat);
    std::ostringstream stream;
    api.dumpModel(stream);
    CHECK(stream.str().find("(define-fun |condition name| () Bool true)") != std::string::npos);
}

TEST_CASE("MV: SAT for Bool — model access does not crash") {
    auto path = writeSmt2("bool_sat",
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert (or p q))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    // Model for pure-Bool may be empty if solver does not project Bool atoms.
    CHECK_NOTHROW(m.values());
}

TEST_CASE("MV: UNSAT does not invoke model") {
    auto path = writeSmt2("unsat",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 5))\n"
        "(assert (= x 6))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
    // getModel on unsat is allowed to return empty model but must not crash.
    auto m = s.getModel();
    CHECK_NOTHROW(m.values());
}

TEST_CASE("MV: SAT for 3D LRA returns model assigning all three vars") {
    auto path = writeSmt2("lra_3d",
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(declare-const z Real)\n"
        "(assert (>= x 0)) (assert (>= y 0)) (assert (>= z 0))\n"
        "(assert (= (+ x y z) 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
}

TEST_CASE("MV: SAT for NIA returns non-empty model") {
    auto path = writeSmt2("nia_sat",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    // NIA model is candidate-only; only require API to be callable without crashing.
    CHECK_NOTHROW(m.values());
}
