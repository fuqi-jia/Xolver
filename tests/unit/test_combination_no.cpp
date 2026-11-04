#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include <filesystem>
#include <fstream>
#include <sstream>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))
#define CHECK_NOT_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) != static_cast<int>(expected))

static std::string writeTempSmt2(const std::string& name, const std::string& content) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_no_" + name + ".smt2");
    std::ofstream(p) << content;
    return p.string();
}

TEST_CASE("NO: UF + LIA shared-variable congruence — unsat") {
    // This is a soundness obligation even while completeness is evolving.
    auto path = writeTempSmt2("uf_lia_share_unsat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 1))\n"
        "(assert (= (f x) 5))\n"
        "(assert (distinct (f 1) 5))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_MESSAGE(static_cast<int>(r) != static_cast<int>(Result::Sat),
                  "EUF<->LIA bridge should not return sat");
}

TEST_CASE("NO: UF + LRA shared-variable equality — sat") {
    auto path = writeTempSmt2("uf_lra_share_sat",
        "(set-logic QF_UFLRA)\n"
        "(declare-fun f (Real) Real)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= x y))\n"
        "(assert (= (f x) (f y)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_MESSAGE(static_cast<int>(r) != static_cast<int>(Result::Unsat), "Equal args under shared eq must give equal images");
}

TEST_CASE("NO: UF + LIA bound-induced disequality — unsat") {
    auto path = writeTempSmt2("uf_lia_bound_unsat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (>= a 0))\n"
        "(assert (<= a 1))\n"
        "(assert (>= b 2))\n"
        "(assert (= (f a) (f b)))\n"
        "(assert (distinct a b))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_NOT_RESULT(r, Result::Unsat);  // f is not necessarily injective — sat
}

TEST_CASE("NO: UF + LIA tight bounds and uninterpreted function — sat") {
    auto path = writeTempSmt2("uf_lia_tight_sat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun g (Int Int) Int)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (= x 5))\n"
        "(assert (= y 10))\n"
        "(assert (> (g x y) 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: UF + LRA distinct + equal-image is unsat") {
    auto path = writeTempSmt2("uf_lra_distinct_unsat",
        "(set-logic QF_UFLRA)\n"
        "(declare-fun f (Real) Real)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= x y))\n"
        "(assert (distinct (f x) (f y)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Unsat);
}

TEST_CASE("NO: pure-LIA case in UFLIA logic (no UF symbols used) — sat") {
    auto path = writeTempSmt2("uflia_pure_lia",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 5))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: pure-EUF case in UFLIA logic (no arithmetic used) — sat") {
    auto path = writeTempSmt2("uflia_pure_euf",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (= a b))\n"
        "(assert (= (f a) (f b)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: concrete UF model preserves coinciding arithmetic witnesses") {
    auto path = writeTempSmt2("shared_numeric_model",
        "(set-logic QF_UFNIA)(declare-const i Int)(declare-const j Int)"
        "(declare-const k Int)(declare-fun f (Int) Int)"
        "(assert (not (<= i (f 5))))(assert (distinct 2 (+ 5 k)))"
        "(assert (< 5 (- 0 i)))(assert (<= (+ k k) (f i)))"
        "(assert (not (< (f (+ 5 (f (- 1)))) 1)))"
        "(assert (= i (f i)))(assert (< j 1))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("NO: Boolean UF arguments share arithmetic truth") {
    for (const std::string domain : {"Int", "Real"}) {
        for (bool formulaFirst : {false, true}) {
            CAPTURE(domain);
            CAPTURE(formulaFirst);
            const std::string equality = "(assert (= p (< x y)))";
            const std::string disequality = "(assert (distinct (f p) (f (< x y))))";
            auto path = writeTempSmt2("bool_argument_comparison",
                "(set-logic " + std::string(domain == "Int" ? "QF_UFLIA" : "QF_UFLRA") + ")"
                "(declare-const p Bool)(declare-const x " + domain + ")"
                "(declare-const y " + domain + ")(declare-fun f (Bool) " + domain + ")" +
                (formulaFirst ? equality + disequality : disequality + equality) + "(check-sat)");
            Solver solver;
            REQUIRE(solver.parseFile(path));
            CHECK((solver.checkSat() == Result::Unsat));
        }
    }
}

TEST_CASE("NO: Boolean UF arguments preserve equality and negation") {
    for (bool wholeEquality : {false, true}) {
        for (bool formulaFirst : {false, true}) {
            CAPTURE(wholeEquality);
            CAPTURE(formulaFirst);
            const std::string relation = wholeEquality ? "(assert (= p (or a b)))"
                                                       : "(assert (distinct p (and a b)))";
            const std::string call = wholeEquality
                ? "(assert (distinct (f (= p (or a b))) (f true)))"
                : "(assert (distinct (f p) (f (not (and a b)))))";
            auto path = writeTempSmt2("bool_argument_connectives",
                "(set-logic QF_UFLIA)(declare-const p Bool)(declare-const a Bool)"
                "(declare-const b Bool)(declare-fun f (Bool) Int)" +
                (formulaFirst ? relation + call : call + relation) + "(check-sat)");
            Solver solver;
            REQUIRE(solver.parseFile(path));
            CHECK((solver.checkSat() == Result::Unsat));
        }
    }
}

TEST_CASE("NO: Boolean-only UF arguments have a two-element domain") {
    for (const std::string domain : {"Int", "Real"}) {
        CAPTURE(domain);
        auto path = writeTempSmt2("bool_argument_pigeonhole",
            "(set-logic " + std::string(domain == "Int" ? "QF_UFLIA" : "QF_UFLRA") + ")"
            "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
            "(declare-fun f (Bool) " + domain + ")"
            "(assert (distinct (f p) (f q)))(assert (distinct (f q) (f r)))"
            "(assert (distinct (f p) (f r)))(check-sat)");
        Solver solver;
        REQUIRE(solver.parseFile(path));
        CHECK((solver.checkSat() == Result::Unsat));
    }
}

TEST_CASE("NO: Boolean UF models retain constant sorts and distinct values") {
    for (const std::string domain : {"Int", "Real"}) {
        for (bool constants : {false, true}) {
            CAPTURE(domain);
            CAPTURE(constants);
            auto path = writeTempSmt2("bool_argument_model",
                "(set-logic " + std::string(domain == "Int" ? "QF_UFLIA" : "QF_UFLRA") + ")"
                "(declare-const p Bool)(declare-const q Bool)"
                "(declare-fun f (Bool) " + domain + ")" +
                (constants ? std::string("(assert (= (f true) 1))(assert (= (f false) 2))")
                           : std::string("(assert (distinct (f p) (f q)))")) + "(check-sat)");
            Solver solver;
            REQUIRE(solver.parseFile(path));
            REQUIRE((solver.checkSat() == Result::Sat));
            CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
            std::ostringstream model;
            solver.dumpModel(model);
            CHECK(model.str().find("U4294967295") == std::string::npos);
        }
    }
}

TEST_CASE("NO: Boolean UF truth bridges survive scoped checks") {
    auto path = writeTempSmt2("bool_argument_scopes",
        "(set-logic QF_UFLIA)(declare-const p Bool)(declare-const q Bool)"
        "(declare-fun f (Bool) Int)(assert (distinct (f p) (f q)))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    auto p = solver.mkConst(solver.boolSort(), "p");
    auto q = solver.mkConst(solver.boolSort(), "q");
    auto equality = solver.mkOp(static_cast<uint32_t>(Kind::Eq), {p, q});
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    solver.push();
    solver.assertFormula(equality);
    CHECK((solver.checkSat() == Result::Unsat));
    solver.pop();
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    CHECK((solver.checkSatAssuming({equality}) == Result::Unsat));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("NO: polarity-derived constants preserve UF congruence") {
    for (const std::string domain : {"Int", "Real"}) {
        for (bool disjunction : {false, true}) {
            const std::string facts = "(and (= x 4) (= (f x) 7) (distinct (f 4) 7))";
            const std::string body = disjunction ? "(not (or (not " + facts + ") false))"
                                                : "(not (=> " + facts + " false))";
            const auto path = writeTempSmt2("polarity_constant_uf_unsat",
                "(set-logic " + std::string(domain == "Int" ? "QF_UFLIA" : "QF_UFLRA") + ")"
                "(declare-const x " + domain + ")(declare-fun f (" + domain + ") " + domain + ")"
                "(assert " + body + ")(check-sat)");
            Solver solver;
            REQUIRE(solver.parseFile(path));
            CHECK((solver.checkSat() == Result::Unsat));
        }
    }
}

TEST_CASE("NO: polarity-derived constants retain satisfying models across scopes") {
    for (const std::string domain : {"Int", "Real"}) {
        const auto path = writeTempSmt2("polarity_constant_uf_sat",
            "(set-logic " + std::string(domain == "Int" ? "QF_UFLIA" : "QF_UFLRA") + ")"
            "(declare-const x " + domain + ")(declare-fun f (" + domain + ") " + domain + ")"
            "(assert (not (=> (and (= x 4) (= (f x) 7)) false)))(check-sat)");
        Solver solver;
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
        auto x = solver.mkConst(domain == "Int" ? solver.intSort() : solver.realSort(), "x");
        auto other = domain == "Int" ? solver.mkInt("5") : solver.mkReal("5");
        auto equality = solver.mkOp(static_cast<uint32_t>(Kind::Eq), {x, other});
        CHECK((solver.checkSatAssuming({equality}) == Result::Unsat));
        solver.push();
        solver.assertFormula(equality);
        CHECK((solver.checkSat() == Result::Unsat));
        solver.pop();
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

TEST_CASE("NO: numeric UF model export preserves aliases and literal arguments") {
    for (const std::string domain : {"Int", "Real"}) {
        for (bool paddingFirst : {false, true}) {
            const auto declare = [&](const std::string& name) {
                return "(declare-const " + name + " " + domain + ")";
            };
            const auto logic = domain == "Int" ? "QF_UFLIA" : "QF_UFLRA";
            const std::string facts = "(assert (= alias x))(assert (distinct (f x) (f 0)))"
                                      "(assert (> (g padding) 9))";
            const auto path = writeTempSmt2("numeric_model_alias",
                "(set-logic " + std::string(logic) + ")" +
                (paddingFirst ? declare("padding") + declare("x") : declare("x") + declare("padding")) +
                declare("alias") + "(declare-fun f (" + domain + ") " + domain + ")"
                "(declare-fun g (" + domain + ") " + domain + ")" + facts + "(check-sat)");
            Solver solver;
            REQUIRE(solver.parseFile(path));
            REQUIRE((solver.checkSat() == Result::Sat));
            std::ostringstream exported;
            solver.dumpModel(exported);
            const auto model = exported.str();
            REQUIRE(model.starts_with("(\n"));
            REQUIRE(model.ends_with(")\n"));
            // Replay every emitted definition against the original assertions.
            // The functions now expand to concrete ite terms: this checks the
            // printed witness, including aliases reconstructed from typed values.
            const auto replayPath = writeTempSmt2("numeric_model_alias_replay",
                "(set-logic " + std::string(logic) + ")" + model.substr(2, model.size() - 4) +
                facts + "(check-sat)");
            Solver replay;
            REQUIRE(replay.parseFile(replayPath));
            CHECK((replay.checkSat() == Result::Sat));
        }
    }
}

TEST_CASE("Model completion: inactive functions have typed interpretations") {
    for (const std::string domain : {"Int", "Real", "Bool", "(_ BitVec 8)",
                                     "(Array Int Int)", "(Array Int (Array Int Bool))", "U"}) {
        CAPTURE(domain);
        const std::string prelude = "(set-logic ALL)" +
            (domain == "U" ? std::string("(declare-sort U 0)") : std::string{});
        const std::string facts = "(assert p)(assert (= (unused x) (unused x)))";
        const auto path = writeTempSmt2("unused_typed_function",
            prelude + "(declare-const p Bool)(declare-const x " + domain + ")"
            "(declare-fun unused (" + domain + ") " + domain + ")" + facts + "(check-sat)");
        Solver solver;
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        std::ostringstream exported;
        solver.dumpModel(exported);
        const auto model = exported.str();
        REQUIRE(model.starts_with("(\n"));
        CHECK(model.find("(define-fun unused ") != std::string::npos);
        const auto replayPath = writeTempSmt2("unused_typed_function_replay",
            prelude + model.substr(2, model.size() - 4) + facts + "(check-sat)");
        Solver replay;
        REQUIRE(replay.parseFile(replayPath));
        CHECK((replay.checkSat() == Result::Sat));
    }
}

TEST_CASE("Model completion: trivial SAT exports a complete empty residual model") {
    const auto path = writeTempSmt2("trivial_residual_model",
        "(set-logic QF_UFLIA)(declare-const x Int)(declare-fun unused (Int) Int)"
        "(assert (and true (= x x)))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    REQUIRE((solver.checkSat() == Result::Sat));
    std::ostringstream exported;
    solver.dumpModel(exported);
    REQUIRE(exported.str().starts_with("(\n"));
    CHECK(exported.str().find("(define-fun unused ") != std::string::npos);
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));

    Solver empty;
    REQUIRE((empty.checkSat() == Result::Sat));
    std::ostringstream emptyModel;
    empty.dumpModel(emptyModel);
    CHECK(emptyModel.str() == "(\n)\n");

    const auto datatypePath = writeTempSmt2("unused_datatype_operators",
        "(set-logic ALL)(declare-datatype D ((a) (b)))"
        "(declare-fun unused (Int) Int)(assert true)(check-sat)");
    Solver datatype;
    REQUIRE(datatype.parseFile(datatypePath));
    REQUIRE((datatype.checkSat() == Result::Sat));
    std::ostringstream datatypeModel;
    datatype.dumpModel(datatypeModel);
    CHECK(datatypeModel.str().find("(define-fun unused ") != std::string::npos);
    CHECK(datatypeModel.str().find("(define-fun is-a ") == std::string::npos);
    CHECK(datatypeModel.str().find("(define-fun is-b ") == std::string::npos);
}

TEST_CASE("Model completion: active functions remain constrained through scopes and assumptions") {
    const auto path = writeTempSmt2("unused_function_scopes",
        "(set-logic QF_UFLIA)(declare-const p Bool)(declare-fun active (Int) Int)"
        "(declare-fun unused (Int) Int)(assert (= p (> (active 1) 7)))"
        "(assert (= (unused 0) (unused 0)))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    const auto p = solver.mkConst(solver.boolSort(), "p");
    const auto notP = solver.mkOp(static_cast<uint32_t>(Kind::Not), {p});
    solver.push();
    solver.assertFormula(p);
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    std::ostringstream positive;
    solver.dumpModel(positive);
    CHECK(positive.str().find("(define-fun unused ") != std::string::npos);
    solver.pop();
    REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));

    // Ackermann abstraction can remove a constrained application from the
    // residual DAG. That is not permission to print a zero interpretation.
    const std::string abstractFacts = "(assert (> (f x) 10))";
    const auto abstractPath = writeTempSmt2("constrained_abstract_function",
        "(set-logic QF_UFNRA)(declare-const x Real)(declare-fun f (Real) Real)" +
        abstractFacts + "(check-sat)");
    Solver abstract;
    REQUIRE(abstract.parseFile(abstractPath));
    const auto result = abstract.checkSat();
    CHECK((result != Result::Unsat));
    if (result == Result::Sat) {
        std::ostringstream model;
        abstract.dumpModel(model);
        if (model.str().find("(define-fun f ") != std::string::npos) {
            REQUIRE(model.str().starts_with("(\n"));
            const auto replayPath = writeTempSmt2("constrained_abstract_function_replay",
                "(set-logic QF_UFNRA)" + model.str().substr(2, model.str().size() - 4) +
                abstractFacts + "(check-sat)");
            Solver replay;
            REQUIRE(replay.parseFile(replayPath));
            CHECK((replay.checkSat() == Result::Sat));
        }
    }
}
