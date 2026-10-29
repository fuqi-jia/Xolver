#include <doctest/doctest.h>
#include "applications/verification/pa/Presburger.h"
#include "algebra/integer/UnaryArithmetic.h"
#include "evidence/PresburgerModel.h"
#include "frontend/parser/adapter.h"
#include "xolver/Solver.h"
#include "xolver/Proof.h"
#include <somtparser/frontend/parser.h>
#include <sstream>
#include <set>
#include <filesystem>
#include <fstream>
#include <unistd.h>

using namespace xolver;

TEST_CASE("native recursive declarations retain acyclic symbols and scoped definitions") {
    using K = SOMTParser::NODE_KIND;
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic ALL)(push 1)"
        "(define-funs-rec ((even ((x Int)) Bool) (odd ((x Int)) Bool))"
        " ((ite (= x 0) true (odd (- x 1))) (ite (= x 0) false (even (- x 1)))))"
        "(assert (even 4))"));
    auto definitions = parser.getRecursiveDefinitions();
    REQUIRE(definitions.size() == 2);
    CHECK(definitions[0].symbol != definitions[0].definition);
    CHECK(definitions[0].definition->getFuncParams()[0] != definitions[1].definition->getFuncParams()[0]);
    std::set<SOMTParser::Node> symbols{definitions[0].symbol, definitions[1].symbol};
    size_t calls = 0;
    for (const auto& definition : definitions) {
        CHECK(definition.symbol->getFuncBody()->isNull());
        std::vector<SOMTParser::Node> pending{definition.definition->getFuncBody()};
        std::set<SOMTParser::Node> visited;
        while (!pending.empty()) {
            auto n = pending.back(); pending.pop_back();
            if (!visited.insert(n).second) continue;
            REQUIRE(visited.size() < 40);
            CHECK(n->getKind() != K::NT_UF_APPLY);
            if (n->isFuncRecApplication()) {
                ++calls;
                CHECK(symbols.count(n->getChild(0)) == 1);
                CHECK(n->getChild(0)->getFuncBody()->isNull());
            }
            for (auto c : SOMTParser::children(n)) pending.push_back(c);
        }
    }
    CHECK(calls == 2);
    auto oldCall = parser.getAssertions().at(0);
    CHECK(oldCall->getChild(0) == definitions[0].symbol);
    CHECK(SOMTParser::dumpSMTLIB2(oldCall) == "(even 4)");
    REQUIRE(parser.parseStr("(pop 1)"));
    CHECK(parser.getRecursiveDefinitions().empty());
    CHECK(parser.getFunctions().empty());
    REQUIRE(parser.parseStr("(define-fun-rec even ((x Int)) Bool (even x))(assert (even 4))"));
    auto current = parser.getRecursiveDefinitions().at(0);
    CHECK(current.symbol != definitions[0].symbol);
    CHECK(parser.getAssertions().at(0) != oldCall);
    CHECK(current.definition->getFuncBody()->getChild(0) == current.symbol);
    // Retained snapshots still refer to the old declarations after pop/redeclare.
    CHECK(oldCall->getChild(0) == definitions[0].symbol);
    REQUIRE(parser.parseStr("(reset)"));
    CHECK(parser.getRecursiveDefinitions().empty());
}

TEST_CASE("native function substitution preserves binders and recursive call arguments") {
    SOMTParser::Parser parser;
    parser.getOptions()->setExpandFunctions(true);
    REQUIRE(parser.parseStr("(set-logic ALL)"
        "(define-fun-rec f ((x Int)) Int (ite (= x 0) 0 (f (- x 1))))"
        "(define-fun g ((x Int)) Int (f (+ x 1)))"
        "(assert (= (g 3) 0))"));
    CHECK(SOMTParser::dumpSMTLIB2(parser.getAssertions().at(0)).find("(f 4)") != std::string::npos);
    for (const auto& [body, expected] : std::vector<std::pair<std::string, Result>>{
        {"(and (= x 3) (forall ((x Int)) (= x x)))", Result::Sat},
        {"(and (= x 3) (forall ((x Int)) (= x 3)))", Result::Unsat},
        {"(let ((x 0)) (forall ((|x| Int)) (= x 0)))", Result::Unsat},
        {"(forall ((x Int)) (let ((|x| 7)) (= x 7)))", Result::Sat},
        {"(and (= x 3) (exists ((x Int)) (and (= x 5) (forall ((x Int)) (= x x)))))", Result::Sat}}) {
        SOMTParser::Parser p;
        p.getOptions()->setExpandFunctions(true);
        REQUIRE(p.parseStr("(set-logic ALL)(define-fun f ((x Int)) Bool " + body + ")"
                           "(assert (f 3))"));
        INFO(body);
        CHECK((pa::decide(p.getAssertions()).result == expected));
    }
}

TEST_CASE("native recursive definitions reject duplicate symbols parameters and ill sorts") {
    for (const auto& source : std::vector<std::string>{
        "(define-fun-rec f ((x Int)) Bool true)(define-fun-rec f ((x Int)) Bool false)",
        "(define-funs-rec ((f ((x Int)) Bool) (f ((y Int)) Bool)) (true false))",
        "(define-funs-rec ((f ((x Int) (x Int)) Bool)) (true))",
        "(define-fun-rec f ((x Int)) Bool x)",
        "(define-fun-rec f ((x Int)) Bool (f true))",
        "(define-fun-rec f ((x Int)) Bool (f x x))"}) {
        SOMTParser::Parser parser;
        INFO(source);
        CHECK_FALSE(parser.parseStr("(set-logic ALL)" + source));
    }
}

TEST_CASE("native PA substitutes fixed affine witnesses and preserves divisibility") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(assert (= y 7000021))(assert (exists ((x Int)) (= (* 1000003 x) y)))", Result::Sat},
        {"(assert (= y 7000022))(assert (exists ((x Int)) (= (* 1000003 x) y)))", Result::Unsat},
        {"(assert (= y (- 7000021)))(assert (exists ((x Int)) (= (* (- 1000003) x) y)))", Result::Sat},
        {"(assert (= y 7000021))(assert (exists ((x Int)) (and (= (* 1000003 x) y) (> x 7))))", Result::Unsat},
        {"(assert (= y 17))(assert (= (mod y 1000003) 17))", Result::Sat},
        {"(assert (forall ((y Int)) (exists ((x Int)) (= (* 2 x) y))))", Result::Unsat},
        {"(assert (forall ((y Int)) (exists ((x Int)) (= (* 2 x) (* 4 y)))))", Result::Sat},
    };
    for (const auto& [text, expected] : cases) {
        CAPTURE(text);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic LIA)(declare-const y Int)" + text));
        auto answer = pa::decide(parser.getAssertions(), {100000, 32, 256}, {.elimination = true, .model = true});
        INFO(answer.reason);
        INFO(answer.modelReason);
        REQUIRE((answer.result == expected));
        REQUIRE(answer.trace);
        if (expected == Result::Sat) {
            REQUIRE(answer.modelEvidence);
            CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
        }
    }
    // Compare bounded quantified equations against concrete integer arithmetic,
    // including negative coefficients, non-divisible right sides and endpoints.
    for (int coefficient = -5; coefficient <= 5; ++coefficient) {
        if (!coefficient) continue;
        for (int rhs = -12; rhs <= 12; ++rhs) {
            auto numeral = [](int n) { return n < 0 ? "(- " + std::to_string(-n) + ")" : std::to_string(n); };
            bool exists = false;
            for (int x = -3; x <= 3; ++x) exists |= coefficient * x == rhs;
            SOMTParser::Parser parser;
            REQUIRE(parser.parseStr("(set-logic LIA)(declare-const y Int)(assert (= y " + numeral(rhs) + "))"
                "(assert (exists ((x Int)) (and (<= (- 3) x) (<= x 3) (= (* " + numeral(coefficient) + " x) y))))"));
            auto answer = pa::decide(parser.getAssertions(), {100000, 32, 256});
            CAPTURE(coefficient);
            CAPTURE(rhs);
            INFO(answer.reason);
            CHECK((answer.result == (exists ? Result::Sat : Result::Unsat)));
        }
    }
}

TEST_CASE("native PA exports independently checkable free-variable model evidence") {
    for (const auto& text : std::vector<std::string>{
            "(declare-const x Int)(assert (= x 123456789012345678901234567890))",
            "(declare-const x Int)(assert (= (mod x (- 3)) 2))(assert (< x (- 10)))",
            "(declare-const p Bool)(declare-const x Int)(assert p)(assert (= (abs x) (ite p 7 8)))",
            "(declare-const x Int)(assert (= (- x x) 0))",
            "(assert (forall ((x Int)) (exists ((y Int)) (> y x))))"}) {
        CAPTURE(text);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic ALL)" + text));
        auto result = pa::decide(parser.getAssertions(), {}, {.model = true});
        INFO(result.reason);
        INFO(result.modelReason);
        REQUIRE((result.result == Result::Sat));
        REQUIRE(result.modelAvailable);
        REQUIRE(result.modelEvidence);
        CHECK(pa::checkModel(*result.modelEvidence).holds == std::optional<bool>(true));
        CHECK_FALSE(pa::checkModel(*result.modelEvidence, 0).holds.has_value());
        CHECK_FALSE(result.trace);
        CHECK_FALSE(pa::decide(parser.getAssertions()).modelEvidence);
    }
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic LIA)(declare-const x Int)(assert (= x 7))"));
    auto result = pa::decide(parser.getAssertions(), {}, {.model = true});
    REQUIRE(result.modelEvidence);
    auto bad = *result.modelEvidence;
    bad.values.at(bad.symbols.at("x")) = 8;
    CHECK(pa::checkModel(bad).holds == std::optional<bool>(false));
    bad = *result.modelEvidence;
    bad.values.clear();
    CHECK(pa::checkModel(bad).holds == std::optional<bool>(false));
}

TEST_CASE("native parser preserves simultaneous lets and every chain operand") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(declare-const x Int)(assert (= x 2))"
         "(assert (let ((x 1) (y x)) (= y x)))", Result::Unsat},
        {"(declare-const x Int)(assert (= x 2))"
         "(assert (let ((x 1) (y x)) (= y 2)))", Result::Sat},
        {"(assert (let ((x 2)) (let ((x 1) (y x)) (= y 2))))", Result::Sat},
        {"(assert (let ((x 2)) (let ((x 1) (y (let ((z x)) z))) (= y 1))))", Result::Unsat},
        {"(declare-const p Bool)(assert (= p true false))", Result::Unsat},
        {"(declare-const p Bool)(assert (= p true true))", Result::Sat},
        {"(declare-const p Bool)(assert (= p false false))", Result::Sat},
        {"(declare-const p Bool)(assert p)(assert (= p false false))", Result::Unsat},
        {"(declare-const x Int)(assert (= x 1 2))", Result::Unsat},
        {"(assert (exists ((x Int)) (< 0 x 1)))", Result::Unsat},
        {"(assert (exists ((x Int)) (> 1 x 0)))", Result::Unsat},
        {"(assert (exists ((x Int)) (<= 1 x 0)))", Result::Unsat},
        {"(assert (exists ((x Int)) (>= 0 x 1)))", Result::Unsat},
        {"(assert (exists ((x Int)) (< 0 x 2 3)))", Result::Sat}
    };
    for (bool preserve : {false, true}) {
        for (const auto& [source, expected] : cases) {
            CAPTURE(source);
            CAPTURE(preserve);
            SOMTParser::Parser parser;
            parser.getOptions()->parsing_preserve_let = preserve;
            REQUIRE(parser.parseStr("(set-logic LIA)" + source + "(check-sat)"));
            NativeTerms terms(parser.getNodeManager());
            for (auto root : parser.getAssertions()) terms.addAssertion(terms.index(root));
            CHECK((pa::decide(terms.native(terms.assertions())).result == expected));
        }
    }
}

TEST_CASE("native public comparison construction retains every chain operand") {
    for (auto kind : {Kind::Lt, Kind::Gt, Kind::Leq, Kind::Geq, Kind::Eq}) {
        CAPTURE(static_cast<unsigned>(kind));
        Solver solver;
        auto x = solver.mkConst(solver.intSort(), "x");
        auto left = solver.mkInt(1), right = solver.mkInt(0);
        if (kind == Kind::Gt || kind == Kind::Geq) std::swap(left, right);
        solver.assertFormula(solver.mkOp(static_cast<uint32_t>(kind), {left, x, right}));
        const auto result = solver.checkSat();
        CAPTURE(static_cast<unsigned>(result));
        CHECK((result == Result::Unsat));
    }
    Solver solver;
    auto p = solver.mkConst(solver.boolSort(), "p");
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq),
        {p, solver.mkBool(true), solver.mkBool(false)}));
    CHECK((solver.checkSat() == Result::Unsat));
}

static NativeTerms nativeQuery(SOMTParser::Parser& parser) {
    NativeTerms terms(parser.getNodeManager());
    for (auto root : parser.getAssertions()) terms.addAssertion(terms.index(root));
    return terms;
}

TEST_CASE("native Boolean distinct preserves constants and negation polarity") {
    for (unsigned arity = 2; arity <= 5; ++arity) {
        for (unsigned mask = 0; mask < (1u << arity); ++mask) {
            std::string formula = "(distinct";
            for (unsigned i = 0; i < arity; ++i)
                formula += (mask & (1u << i)) ? " true" : " false";
            formula += ")";
            CAPTURE(formula);
            SOMTParser::Parser parser;
            REQUIRE(parser.parseStr("(set-logic LIA)(assert " + formula + ")(check-sat)"));
            auto native = nativeQuery(parser);
            auto expected = arity == 2 && (mask == 1 || mask == 2) ? Result::Sat : Result::Unsat;
            CHECK((pa::decide(native.native(native.assertions())).result == expected));
        }
    }
    for (unsigned mask = 0; mask < 16; ++mask) {
        const bool p = mask & 1, q = mask & 2, negateP = mask & 4, negateQ = mask & 8;
        const std::string left = negateP ? "(not p)" : "p";
        const std::string right = negateQ ? "(not q)" : "q";
        const std::string assignments = std::string("(assert (= p ") + (p ? "true" : "false") +
            "))(assert (= q " + (q ? "true" : "false") + "))";
        const auto expected = (p != negateP) != (q != negateQ) ? Result::Sat : Result::Unsat;
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic LIA)(declare-const p Bool)(declare-const q Bool)" +
            assignments + "(assert (distinct " + left + " " + right + "))(check-sat)"));
        auto native = nativeQuery(parser);
        CAPTURE(mask);
        CHECK((pa::decide(native.native(native.assertions())).result == expected));
        // The binary construction API has its own Boolean simplifications.
        auto a = parser.declareVar("p", "Bool"), b = parser.declareVar("q", "Bool");
        if (negateP) a = parser.mkNot(a);
        if (negateQ) b = parser.mkNot(b);
        NativeTerms direct(parser.getNodeManager());
        direct.addAssertion(direct.index(parser.mkDistinct(a, b)));
        direct.addAssertion(direct.index(p ? parser.declareVar("p", "Bool") :
                                         parser.mkNot(parser.declareVar("p", "Bool"))));
        direct.addAssertion(direct.index(q ? parser.declareVar("q", "Bool") :
                                         parser.mkNot(parser.declareVar("q", "Bool"))));
        CHECK((pa::decide(direct.native(direct.assertions())).result == expected));
    }
}

TEST_CASE("native PA consumes the parser DAG with restored shadowed bindings") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(forall ((x Int)) (exists ((y Int)) (> y x)))", Result::Sat},
        {"(exists ((x Int)) (forall ((y Int)) (> x y)))", Result::Unsat},
        {"(exists ((x Int)) (and (exists ((x Int)) (= x 0)) (= x 1)))", Result::Sat},
        {"(forall ((x Int)) (and (exists ((x Int)) (= x 0)) (= x 1)))", Result::Unsat},
        {"(forall ((x Int)) (let ((y (+ x 1))) (exists ((z Int)) (= z y))))", Result::Sat},
        {"(forall ((x Int)) (and (= x (+ (* 3 (div x 3)) (mod x 3)))"
         " (<= 0 (mod x 3)) (< (mod x 3) 3)))", Result::Sat}
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic LIA)(assert " + formula + ")(check-sat)"));
        auto input = nativeQuery(parser);
        REQUIRE(pa::hasQuantifiers(input.native(input.assertions())));
        CHECK((pa::decide(input.native(input.assertions())).result == expected));
        FrontendAdapter adapter(parser);
        auto rewritten = adapter.importProblem();
        CHECK((pa::decide(rewritten->native(rewritten->assertions())).result == expected));
    }
}

TEST_CASE("native binders have declaration identity and restore different-sort shadows") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic ALL)(assert (exists ((x Int))"
        " (and (exists ((x Bool)) x) (= x 7))))"));
    const auto outer = parser.getAssertions().at(0);
    const auto outerBinder = outer->getChild(1);
    SOMTParser::Node inner, equality;
    // The parser canonicalizes commutative children; neither conjunction
    // order nor equality operand order is a source-order guarantee.
    for (auto child : SOMTParser::children(outer->getChild(0))) {
        if (child->getKind() == SOMTParser::NODE_KIND::NT_EXISTS) inner = child;
        if (child->getKind() == SOMTParser::NODE_KIND::NT_EQ) equality = child;
    }
    REQUIRE(inner);
    REQUIRE(equality);
    const auto innerBinder = inner->getChild(1);
    CHECK(outerBinder != innerBinder);
    CHECK_FALSE(SOMTParser::NodeEqual{}(outerBinder, innerBinder));
    CHECK(outerBinder->getSort()->isInt());
    CHECK(innerBinder->getSort()->isBool());
    CHECK(inner->getChild(0) == innerBinder);
    CHECK((equality->getChild(0) == outerBinder || equality->getChild(1) == outerBinder));
    auto terms = nativeQuery(parser);
    CHECK((pa::decide(terms.native(terms.assertions())).result == Result::Sat));
}

TEST_CASE("native PA scopes Boolean domains and piecewise integer witnesses") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(forall ((p Bool)) p)", Result::Unsat},
        {"(exists ((p Bool)) (not p))", Result::Sat},
        {"(forall ((p Bool)) (or p (not p)))", Result::Sat},
        {"(forall ((p Bool)) (exists ((q Bool)) (distinct p q)))", Result::Sat},
        {"(exists ((p Bool)) (forall ((q Bool)) (distinct p q)))", Result::Unsat},
        {"(forall ((x Int)) (exists ((p Bool)) (= p (>= x 0))))", Result::Sat},
        {"(exists ((p Bool)) (forall ((x Int)) (= p (>= x 0))))", Result::Unsat},
        {"(forall ((p Bool)) (exists ((x Int)) (= x (ite p 3 (- 2)))))", Result::Sat},
        {"(exists ((x Int)) (forall ((p Bool)) (= x (ite p 3 (- 2)))))", Result::Unsat},
        {"(forall ((p Bool) (x Int)) (= (ite p x (- x)) (ite (not p) (- x) x)))", Result::Sat},
        {"(forall ((p Bool)) (=> p false p))", Result::Sat},
        {"(exists ((p Bool)) (xor p p p))", Result::Sat},
        {"(exists ((p Bool)) (xor p p p p))", Result::Unsat},
        {"(exists ((p Bool) (q Bool) (r Bool)) (distinct p q r))", Result::Unsat},
        {"(forall ((x Int)) (= (abs x) (ite (>= x 0) x (- x))))", Result::Sat},
        {"(forall ((x Int)) (= (abs x) x))", Result::Unsat},
        {"(not (forall ((x Int)) (< (abs x) 0)))", Result::Sat},
        {"(forall ((x Int)) (exists ((y Int)) (= (abs y) x)))", Result::Unsat},
        {"(forall ((x Int)) (exists ((y Int)) (and (>= y 0) (= y (abs x)))))", Result::Sat},
        {"(exists ((x Int)) (and (= (abs x) 5) (< x 0)))", Result::Sat},
        {"(exists ((x Int)) (and (= (abs x) 5) (= x 0)))", Result::Unsat},
        {"(forall ((x Int)) (not (= (ite (> x 0) x (- x)) 0)))", Result::Unsat},
        {"(forall ((x Int)) (= (ite (forall ((y Int)) (>= (+ y x) y)) x (- x))"
         " (abs x)))", Result::Sat},
        {"(forall ((x Int)) (= (+ (* (- 3) (div (abs x) (- 3)))"
         " (mod (abs x) (- 3))) (abs x)))", Result::Sat},
        {"(forall ((x Int)) (= (ite (= (mod x 2) 0) (div x 2) (- (div x 2)))"
         " (ite (= (mod x 2) 0) (div x 2) (- (div x 2)))))", Result::Sat}
    };
    for (bool preserve : {false, true}) {
        for (const auto& [formula, expected] : cases) {
            CAPTURE(formula);
            CAPTURE(preserve);
            SOMTParser::Parser parser;
            parser.getOptions()->parsing_preserve_let = preserve;
            REQUIRE(parser.parseStr("(set-logic LIA)(assert " + formula + ")(check-sat)"));
            auto native = nativeQuery(parser);
            auto decision = pa::decide(native.native(native.assertions()));
            INFO(decision.reason);
            CHECK((decision.result == expected));
            FrontendAdapter adapter(parser);
            auto rewritten = adapter.importProblem();
            auto second = pa::decide(rewritten->native(rewritten->assertions()));
            INFO(second.reason);
            CHECK((second.result == expected));
        }
    }
}

TEST_CASE("native PA reconstructs free models through scoped piecewise definitions") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic LIA)(declare-const x Int)(declare-const p Bool)"
        "(assert (= (abs x) 7))(assert (< x 0))"
        "(assert (forall ((q Bool)) (= (ite q x (- x)) (ite q (- 7) 7))))"
        "(assert (forall ((y Int)) (= (ite p (+ y x) (- y x)) (- y 7))))"
        "(check-sat)"));
    auto native = nativeQuery(parser);
    auto decision = pa::decide(native.native(native.assertions()));
    INFO(decision.reason);
    REQUIRE((decision.result == Result::Sat));
    INFO(decision.modelReason);
    REQUIRE(decision.modelAvailable);
    CHECK(decision.model.at("x") == "-7");
    CHECK(decision.model.at("p") == "true");
    CHECK(decision.model.size() == 2); // no bound variables or local witnesses
}

TEST_CASE("public PA solving retains the native DAG and invalidates stale cores") {
    const auto path = std::filesystem::temp_directory_path() /
        ("xolver-native-pa-" + std::to_string(getpid()) + ".smt2");
    struct Remove { std::filesystem::path path; ~Remove() { std::filesystem::remove(path); } } remove{path};
    { std::ofstream file(path); file << "(set-logic LIA)(assert (forall ((x Int)) (= x 0)))"; }
    Solver solver;
    REQUIRE(solver.parseFile(path.string()));
    REQUIRE((solver.checkSat() == Result::Unsat));
    std::ostringstream features, core;
    solver.dumpFeatures(features);
    CHECK(features.str().find("\"formula_storage\":\"somtparser\"") != std::string::npos);
    CHECK(features.str().find("\"legacy_nodes\":0") != std::string::npos);
    CHECK(features.str().find("\"vars\":0") != std::string::npos);
    CHECK(features.str().find("\"int\":true") != std::string::npos);
    CHECK(features.str().find("\"nonlinear\":false") != std::string::npos);
    CHECK(features.str().find("\"array\":false") != std::string::npos);
    solver.dumpUnsatCore(core);
    CHECK(core.str().find("forall") != std::string::npos);
    // Mutating native assertions must invalidate the previous result.
    solver.push();
    CHECK(solver.getUnsatCore().empty());
    REQUIRE((solver.checkSat() == Result::Unsat));
    solver.pop();
    CHECK(solver.getUnsatCore().empty());
    REQUIRE(solver.parseFile(path.string()));
    REQUIRE((solver.checkSat() == Result::Unsat));
    CHECK_FALSE(solver.getUnsatCore().empty());
    { std::ofstream file(path); file << "(set-logic LIA)(declare-const x Int)"
        "(assert (forall ((y Int)) (=> (>= y x) (>= y 5))))"; }
    REQUIRE(solver.parseFile(path.string()));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Indeterminate));
    // Requesting the model must not make validation accidentally
    // succeed on an empty list of original assertions.
    solver.getModel();
    CHECK((solver.validateModel() == Solver::ModelValidation::Indeterminate));
    auto symbol = solver.mkConst(solver.intSort(), "x");
    REQUIRE(solver.getModel().getValue(symbol.id()) != nullptr);
}

TEST_CASE("PA reconstructs large negative integers, congruences and free Booleans") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic LIA)(declare-const x Int)(declare-const z Int)"
        "(declare-const p Bool)(assert p)(assert (<= x (- 1000000000000000000000000)))"
        "(assert (= (mod x 7) 3))(assert (= z (+ (* 3 x) 5)))"
        "(assert (forall ((y Int)) (exists ((w Int)) (= w (+ x y)))))"));
    auto native = nativeQuery(parser);
    auto decision = pa::decide(native.native(native.assertions()));
    REQUIRE((decision.result == Result::Sat));
    REQUIRE(decision.modelAvailable);
    CHECK(decision.model.at("p") == "true");
    mpz_class x(decision.model.at("x")), z(decision.model.at("z"));
    CHECK(x <= mpz_class("-1000000000000000000000000"));
    mpz_class residue;
    mpz_fdiv_r_ui(residue.get_mpz_t(), x.get_mpz_t(), 7);
    CHECK(residue == 3);
    CHECK(z == 3 * x + 5);
    // Optional native rewriting must preserve the decision and reconstructed model.
    FrontendAdapter adapter(parser);
    auto rewritten = adapter.importProblem();
    auto second = pa::decide(rewritten->native(rewritten->assertions()));
    REQUIRE(second.modelAvailable);
    mpz_class lx(second.model.at("x")), lz(second.model.at("z"));
    CHECK(lx <= mpz_class("-1000000000000000000000000"));
    CHECK(lz == 3 * lx + 5);
    CHECK(second.model.at("p") == "true");
}

TEST_CASE("native PA produces complete scoped QE obligations without compatibility terms") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(forall ((x Int)) (exists ((y Int)) (= y (+ x 1))))", Result::Sat},
        {"(exists ((x Int)) (forall ((y Int)) (> x y)))", Result::Unsat},
        {"(forall ((x Int)) (= x (+ (* (- 3) (div x (- 3))) (mod x (- 3)))))", Result::Sat},
        {"(forall ((p Bool)) (exists ((x Int)) (= (abs x) (ite p 4 7))))", Result::Sat},
        {"(exists ((x Int)) (and (= (mod x 6) 2) (= (mod x 4) 1)))", Result::Unsat},
        {"(exists ((x Int)) (= (* 10000000000000000000000000000000000000000 x) 1))", Result::Unsat}
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        SOMTParser::Parser parser;
        parser.getOptions()->parsing_preserve_let = true;
        REQUIRE(parser.parseStr("(set-logic LIA)(assert " + formula + ")"));
        const auto decision = pa::decide(parser.getAssertions(), {}, {.elimination = true});
        INFO(decision.reason);
        REQUIRE((decision.result == expected));
        REQUIRE(decision.trace.has_value());
        CHECK(decision.trace->steps.size() == decision.eliminated);
        CHECK_FALSE(decision.trace->steps.empty());
        for (const auto& step : decision.trace->steps)
            for (const auto& cube : step.after)
                for (const auto& atom : cube)
                    CHECK(atom.affine.coefficient(step.variable) == 0);
        CHECK((decision.trace->closed.empty() == (expected == Result::Unsat)));
        CHECK_FALSE(pa::decide(parser.getAssertions()).trace.has_value());
        pa::Limits limits; limits.work = 1;
        auto exhausted = pa::decide(parser.getAssertions(), limits, {.elimination = true});
        CHECK((exhausted.result == Result::Unknown));
        CHECK_FALSE(exhausted.trace.has_value());
    }
}

TEST_CASE("native PA certificate API invalidates evidence on query mutation and unknown") {
    Solver solver;
    solver.setOption("produce-pa-certificate", OptionValue(true));
    auto x = solver.mkConst(solver.intSort(), "x");
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {x, solver.mkInt(9)}));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK(solver.getProof().presburger().find("generated-unchecked") != std::string::npos);
    solver.push();
    CHECK(solver.getProof().isEmpty());
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Lt), {x, solver.mkInt(0)}));
    REQUIRE((solver.checkSat() == Result::Unsat));
    CHECK_FALSE(solver.getProof().presburger().empty());
    solver.pop();
    CHECK(solver.getProof().isEmpty());
    REQUIRE((solver.checkSat() == Result::Sat));
    solver.setRuntimeParameter("XOLVER_PA_WORK", "1");
    CHECK((solver.checkSat() == Result::Unknown));
    CHECK(solver.getProof().isEmpty());
    solver.reset();
    solver.setRuntimeParameter("XOLVER_PA_WORK", "2000000");
    CHECK((solver.checkSat() == Result::Sat));
    CHECK_FALSE(solver.getProof().presburger().empty());
}

TEST_CASE("native PA accepts standard indexed divisibility") {
    const std::vector<std::pair<std::string, Result>> cases{
        {"(assert (forall ((x Int)) ((_ divisible 1000003) (* 1000003 x))))", Result::Sat},
        {"(assert (forall ((x Int)) ((_ divisible 2) x)))", Result::Unsat},
        {"(assert (exists ((x Int)) (and ((_ divisible 6) x) (= (mod x 4) 1))))", Result::Unsat},
    };
    for (const auto& [source, expected] : cases) {
        CAPTURE(source);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic LIA)" + source));
        auto answer = pa::decide(parser.getAssertions(), {2000000, 32, 256},
                                 {.elimination = true, .model = true});
        INFO(answer.reason);
        INFO(answer.modelReason);
        REQUIRE((answer.result == expected));
        REQUIRE(answer.trace);
        if (expected == Result::Sat) {
            REQUIRE(answer.modelEvidence);
            CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
        }
    }
}

TEST_CASE("native PA nary division agrees with left associated binary division") {
    for (const auto& divisors : std::vector<std::vector<int>>{{2, 2}, {3, -2}, {-3, -2}, {-3, 2, -2}}) {
        SOMTParser::Parser parser;
        auto x = parser.declareVar("x", "Int");
        std::vector<SOMTParser::Node> operands{x};
        auto nested = x;
        for (int divisor : divisors) {
            auto constant = parser.mkConstInt(divisor);
            operands.push_back(constant);
            nested = parser.mkDivInt(nested, constant);
        }
        auto nary = parser.mkDivInt(operands);
        REQUIRE(nary->getChildrenSize() == operands.size());
        // A satisfiable difference would be an actual integer counterexample.
        auto unequal = pa::decide({parser.mkNot(parser.mkEq(nary, nested))},
                                  {2000000, 32, 256}, {.elimination = true});
        INFO(unequal.reason);
        REQUIRE((unequal.result == Result::Unsat));
        REQUIRE(unequal.trace);
        for (int value : {-13, -1, 0, 1, 13}) {
            mpz_class expected = value;
            for (int divisor : divisors) {
                const mpz_class modulus = std::abs(divisor);
                mpz_fdiv_q(expected.get_mpz_t(), expected.get_mpz_t(), modulus.get_mpz_t());
                if (divisor < 0) expected = -expected;
            }
            auto answer = pa::decide({parser.mkEq(x, parser.mkConstInt(value)),
                                      parser.mkEq(nary, parser.mkConstInt(expected.get_str()))},
                                     {2000000, 32, 256}, {.model = true});
            INFO(answer.reason);
            REQUIRE((answer.result == Result::Sat));
            REQUIRE(answer.modelEvidence);
            CHECK(answer.model.at("x") == std::to_string(value));
            CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
        }
    }
    // The folded chain's quotient must not alias a surrounding binary div
    // merely because the binary dividend is the very same chain node.
    SOMTParser::Parser parser;
    auto x = parser.declareVar("x", "Int");
    auto two = parser.mkConstInt(2), four = parser.mkConstInt(4);
    auto chain = parser.mkDivInt(std::vector<SOMTParser::Node>{x, two, two});
    auto outer = parser.mkDivInt(chain, four);
    for (int value : {5, 20}) {
        auto answer = pa::decide({parser.mkEq(x, parser.mkConstInt(80)),
                                  parser.mkEq(outer, parser.mkConstInt(value))});
        CHECK((answer.result == (value == 5 ? Result::Sat : Result::Unsat)));
    }
}

TEST_CASE("native PA solves large positive and negative congruences without residue enumeration") {
    const std::vector<std::pair<std::string, Result>> cases{
        {"(assert (= (mod x 1000003) 123456))", Result::Sat},
        {"(assert (= (mod x 1000003) 123456))(assert (= (mod x 1000033) 654321))", Result::Sat},
        {"(assert (= (mod x 6000018) 2))(assert (= (mod x 4000012) 1))", Result::Unsat},
        {"(assert (= (mod x 6000018) 2))(assert (= (mod x 4000012) 2))", Result::Sat},
        {"(assert (= (mod (* (- 6) x) 1000003) 17))", Result::Sat},
        {"(assert (= (mod x 1000003) 17))(assert (not ((_ divisible 3) x)))"
         "(assert (< x (- 1000000000000000000000000000000)))", Result::Sat},
        {"(assert (= (mod x 1000003) 17))(assert (<= 0 x))(assert (< x 17))", Result::Unsat},
        {"(assert (= (mod x 1000003) 17))(assert (<= 0 x))(assert (<= x 17))", Result::Sat},
        {"(assert (not ((_ divisible 1000000000000000000000000000003) x)))"
         "(assert (not ((_ divisible 1000000000000000000000000000033) (+ x 1))))", Result::Sat},
        {"(assert (not ((_ divisible 2) x)))(assert (not ((_ divisible 2) (+ x 1))))", Result::Unsat},
        {"(assert (not ((_ divisible 2) x)))(assert (not ((_ divisible 4) (+ x 1))))"
         "(assert (not ((_ divisible 4) (+ x 3))))", Result::Unsat},
        {"(assert (not ((_ divisible 2) x)))(assert (not ((_ divisible 4) (+ x 1))))"
         "(assert (< x 0))(assert (>= x (- 2)))", Result::Unsat},
        {"(assert (not ((_ divisible 2) x)))(assert (not ((_ divisible 4) (+ x 1))))"
         "(assert (< x 0))(assert (>= x (- 3)))", Result::Sat},
    };
    for (const auto& [source, expected] : cases) {
        CAPTURE(source);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic LIA)(declare-const x Int)" + source));
        // A modulus is not itself a work cost: this bound allows no old Cooper
        // residue sweep, but exact CRT/counting still has to honor work limits.
        auto answer = pa::decide(parser.getAssertions(), {100000, 1, 256},
                                 {.elimination = true, .model = true});
        INFO(answer.reason);
        INFO(answer.modelReason);
        REQUIRE((answer.result == expected));
        REQUIRE(answer.trace);
        if (expected == Result::Sat) {
            REQUIRE(answer.modelAvailable);
            REQUIRE(answer.modelEvidence);
            CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
            auto corrupted = *answer.modelEvidence;
            corrupted.values.clear();
            CHECK(pa::checkModel(corrupted).holds == std::optional<bool>(false));
        }
        auto exhausted = pa::decide(parser.getAssertions(), {1, 1, 256},
                                    {.elimination = true, .model = true});
        CHECK((exhausted.result == Result::Unknown));
        CHECK_FALSE(exhausted.trace);
        CHECK_FALSE(exhausted.modelEvidence);
    }
}

TEST_CASE("native PA congruence projection matches bounded exhaustive integer semantics") {
    auto numeral = [](int n) { return n < 0 ? "(- " + std::to_string(-n) + ")" : std::to_string(n); };
    for (int index = 0; index < 240; ++index) {
        const int a = index % 7 - 3, b = (index * 3) % 9 - 4;
        const int m = index % 9 + 2, n = (index * 7) % 11 + 2;
        const int c = (index * 11) % 19 - 9, d = (index * 13) % 17 - 8;
        const int lower = index % 11 - 12, upper = lower + index % 13;
        const bool positive = index % 3 == 0;
        auto divisible = [&](int coefficient, int constant, int modulus) {
            return "((_ divisible " + std::to_string(modulus) + ") (+ (* " + numeral(coefficient) + " x) " + numeral(constant) + "))";
        };
        std::string first = divisible(a, c, m), second = divisible(b, d, n);
        if (!positive) first = "(not " + first + ")";
        std::string body = "(and (<= " + numeral(lower) + " x) (<= x " + numeral(upper) + ") " + first + " (not " + second + "))";
        bool exists = false;
        for (int x = lower; x <= upper; ++x)
            exists |= (((a * x + c) % m == 0) == positive) && (b * x + d) % n != 0;
        CAPTURE(index);
        CAPTURE(body);
        for (bool quantified : {false, true}) {
            SOMTParser::Parser parser;
            REQUIRE(parser.parseStr("(set-logic LIA)" +
                (quantified ? "(assert (exists ((x Int)) " + body + "))" :
                              "(declare-const x Int)(assert " + body + ")")));
            auto answer = pa::decide(parser.getAssertions(), {100000, 1, 256}, {.model = true});
            INFO(answer.reason);
            INFO(answer.modelReason);
            REQUIRE((answer.result == (exists ? Result::Sat : Result::Unsat)));
            if (exists) {
                REQUIRE(answer.modelEvidence);
                CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
                if (!quantified) {
                    const int x = std::stoi(answer.model.at("x"));
                    CHECK(x >= lower);
                    CHECK(x <= upper);
                    CHECK((((a * x + c) % m == 0) == positive));
                    CHECK((b * x + d) % n != 0);
                }
            }
        }
    }
}

TEST_CASE("native PA numeric kernel counts intersecting exclusions exactly") {
    for (int seed = 0; seed < 160; ++seed) {
        pa::Cube cube;
        cube.push_back({pa::Affine{{{0, -1}}, -40}});
        cube.push_back({pa::Affine{{{0, 1}}, -40}});
        for (int i = 0; i < 6; ++i) {
            int coefficient = (seed * (i + 1) + i * 3) % 9 - 4;
            if (!coefficient) coefficient = 1;
            const int constant = (seed * 7 + i * 13) % 29 - 14;
            const int divisor = (seed + i * 5) % 12 + 2;
            cube.push_back({pa::Affine{{{0, coefficient}}, constant}, divisor,
                            !(i == 0 && seed % 3 == 0)});
        }
        auto holds = [&](int value) {
            for (const auto& literal : cube) {
                const mpz_class evaluated = literal.affine.constant + literal.affine.coefficient(0) * value;
                const bool satisfied = literal.divisor == 0 ? evaluated <= 0 :
                    bool(mpz_divisible_p(evaluated.get_mpz_t(), literal.divisor.get_mpz_t())) != literal.negatedDivisibility;
                if (!satisfied) return false;
            }
            return true;
        };
        bool expected = false;
        for (int x = -40; x <= 40; ++x) expected |= holds(x);
        std::size_t work = 0;
        pa::detail::UnaryArithmetic arithmetic([&](std::size_t n) { work += n; });
        auto witness = arithmetic.solve(cube, 0);
        CAPTURE(seed);
        CHECK(bool(witness) == expected);
        CHECK(work > 0);
        if (witness) {
            REQUIRE(*witness >= -40);
            REQUIRE(*witness <= 40);
            CHECK(holds(witness->get_si()));
        }
    }
}

TEST_CASE("native PA nary division preserves arbitrary precision and rejects nonpositive indexed moduli") {
    const mpz_class magnitude("123456789012345678901234567890123456789012345678901234567890123456789");
    const std::vector<mpz_class> divisors{1000003, -1000033, 1000037};
    for (int sign : {-1, 1}) {
        const mpz_class value = sign * magnitude;
        mpz_class expected = value;
        SOMTParser::Parser parser;
        auto x = parser.declareVar("x", "Int");
        std::vector<SOMTParser::Node> operands{x};
        for (const auto& divisor : divisors) {
            operands.push_back(parser.mkConstInt(divisor.get_str()));
            const mpz_class modulus = abs(divisor);
            mpz_fdiv_q(expected.get_mpz_t(), expected.get_mpz_t(), modulus.get_mpz_t());
            if (divisor < 0) expected = -expected;
        }
        auto answer = pa::decide({parser.mkEq(x, parser.mkConstInt(value.get_str())),
                                  parser.mkEq(parser.mkDivInt(operands), parser.mkConstInt(expected.get_str()))},
                                 {300000, 1, 256}, {.elimination = true, .model = true});
        INFO(answer.reason);
        REQUIRE((answer.result == Result::Sat));
        REQUIRE(answer.modelAvailable);
        CHECK(answer.model.at("x") == value.get_str());
        REQUIRE(answer.modelEvidence);
        CHECK(pa::checkModel(*answer.modelEvidence).holds == std::optional<bool>(true));
    }
    // SMT-LIB's ranked operator admits positive numerals only. If a native
    // producer nevertheless supplies zero, do not reinterpret it as x = 0.
    SOMTParser::Parser parser;
    auto x = parser.declareVar("x", "Int");
    auto malformed = parser.mkIsDivisible(x, parser.mkConstInt(SOMTParser::Integer(0)));
    auto answer = pa::decide({malformed}, {}, {.elimination = true, .model = true});
    CHECK((answer.result == Result::Unknown));
    CHECK(answer.reason == "PA divisibility requires a positive constant modulus");
    CHECK_FALSE(answer.trace);
    CHECK_FALSE(answer.modelEvidence);
}
