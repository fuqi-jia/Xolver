#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/boolean/Atomizer.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/coordination/TheoryManager.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include "algebra/linear/LinearExpr.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/lra/GeneralSimplex.h"
#include "search/combination/CareGraph.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

TEST_CASE("LIA sharing: fixed-value bases retain explanations across withdrawal and late terms") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    ir.registerSort(1, SortKind::Bool);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    TheoryLemmaDatabase lemmas;
    std::vector<std::string> names;
    std::vector<ExprId> expressions;
    std::vector<SharedTermId> terms;
    std::vector<bool> pinned;
    std::vector<int> values;
    std::vector<SatLit> sources;
    auto addTerm = [&] {
        names.push_back("member_" + std::to_string(names.size()));
        expressions.push_back(ir.add({Kind::Variable, 0, {}, Payload(names.back())}));
        terms.push_back(shared.getOrCreate(expressions.back(), 0, names.back(), false));
        shared.addOwner(terms.back(), TheoryId::LIA);
        shared.addOwner(terms.back(), TheoryId::EUF);
        pinned.push_back(false);
        values.push_back(0);
        sources.push_back({0, true});
    };
    auto pin = [&](size_t index, int value, SatVar variable, int level) {
        sources[index] = {variable, true};
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{names[index], 1}}}, Relation::Eq,
                              RealValue::fromInt(value)}}, true, level, sources[index]);
        pinned[index] = true;
        values[index] = value;
    };
    auto verify = [&](size_t edges) {
        REQUIRE(solver.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
        const auto facts = solver.getDeducedSharedEqualities();
        CHECK(facts.size() == edges);
        std::vector<std::vector<bool>> reached(terms.size(), std::vector<bool>(terms.size(), false));
        for (size_t i = 0; i < terms.size(); ++i) reached[i][i] = true;
        for (const auto& fact : facts) {
            const auto first = std::find(terms.begin(), terms.end(), fact.a);
            const auto second = std::find(terms.begin(), terms.end(), fact.b);
            REQUIRE(first != terms.end());
            REQUIRE(second != terms.end());
            const size_t a = first - terms.begin(), b = second - terms.begin();
            CHECK(pinned[a]);
            CHECK(pinned[b]);
            CHECK(values[a] == values[b]);
            for (const auto endpoint : {a, b})
                CHECK(std::find(fact.reasons.begin(), fact.reasons.end(), sources[endpoint]) != fact.reasons.end());
            for (const auto reason : fact.reasons) {
                bool active = false;
                for (size_t i = 0; i < terms.size(); ++i)
                    active |= pinned[i] && reason == sources[i];
                CHECK(active);
            }
            reached[a][b] = reached[b][a] = true;
        }
        for (size_t k = 0; k < terms.size(); ++k)
            for (size_t i = 0; i < terms.size(); ++i)
                for (size_t j = 0; j < terms.size(); ++j)
                    reached[i][j] = reached[i][j] || (reached[i][k] && reached[k][j]);
        for (size_t i = 0; i < terms.size(); ++i)
            for (size_t j = 0; j < terms.size(); ++j)
                CHECK(reached[i][j] == (i == j || (pinned[i] && pinned[j] && values[i] == values[j])));
    };
    for (size_t i = 0; i < 8; ++i) addTerm();
    for (size_t i = 0; i < 8; ++i)
        pin(i, i < 4 ? 2 : 5, static_cast<SatVar>(i + 1), i < 4 ? 0 : 1);
    verify(6);
    solver.backtrackToLevel(0);
    for (size_t i = 4; i < 8; ++i) pinned[i] = false;
    verify(3);
    for (size_t i = 4; i < 8; ++i) pin(i, 2, static_cast<SatVar>(20 + i), 1);
    verify(7);
    solver.backtrackToLevel(0);
    for (size_t i = 4; i < 8; ++i) pinned[i] = false;
    addTerm();
    pin(8, 2, 40, 1);
    verify(4);
    solver.backtrackToLevel(0);
    pinned[8] = false;
    const auto application = ir.add({Kind::UFApply, 0, {expressions[3]}, Payload(std::string("f"))});
    const auto zero = ir.add({Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ir.addAssertion(ir.add({Kind::Eq, 1, {application, zero}, Payload{}}));
    CareGraph care;
    care.build(ir, shared);
    solver.setCareGraph(&care);
    verify(3);
    for (const auto& fact : solver.getDeducedSharedEqualities())
        CHECK((fact.a == terms[3] || fact.b == terms[3]));
}

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_lia.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("LIA: unbounded Boolean integer models survive widening and query scopes") {
    Solver solver;
    solver.setLogic("QF_LIA");
    auto op = [&](Kind kind, std::vector<Term> terms) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(terms));
    };
    const auto x = solver.mkConst(solver.intSort(), "unbounded-x");
    const auto y = solver.mkConst(solver.intSort(), "unbounded-y");
    const auto choice = solver.mkConst(solver.boolSort(), "unbounded-choice");
    const auto negativeChoice = op(Kind::Not, {choice});
    auto checkChoice = [&](bool expected) {
        const auto model = solver.getModel();
        const auto* value = model.getValue(choice.id());
        REQUIRE(value != nullptr);
        CHECK(*value == (expected ? "true" : "false"));
    };
    solver.assertFormula(op(Kind::Or, {
        op(Kind::And, {choice, op(Kind::Gt, {x, solver.mkInt(2)}),
            op(Kind::Eq, {y, op(Kind::Add, {op(Kind::Mul, {solver.mkInt(2), x}), solver.mkInt(1)})})}),
        op(Kind::And, {negativeChoice, op(Kind::Lt, {x, solver.mkInt(-2)}),
            op(Kind::Eq, {y, op(Kind::Sub, {op(Kind::Mul, {solver.mkInt(3), x}), solver.mkInt(1)})})})}));
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    solver.push();
    solver.assertFormula(op(Kind::Geq, {x, solver.mkInt(17)}));
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    checkChoice(true);
    solver.pop();
    REQUIRE(static_cast<int>(solver.checkSatAssuming({negativeChoice})) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    checkChoice(false);
    solver.push();
    solver.assertFormula(op(Kind::Lt, {x, solver.mkInt(-17)}));
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    checkChoice(false);
    solver.pop();
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("LIA: unbounded Boolean integer contradictions retain the explained fallback") {
    Solver solver;
    solver.setLogic("QF_LIA");
    auto op = [&](Kind kind, std::vector<Term> terms) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(terms));
    };
    const auto x = solver.mkConst(solver.intSort(), "parity-x");
    const auto y = solver.mkConst(solver.intSort(), "parity-y");
    const auto impossible = op(Kind::Or, {
        op(Kind::Eq, {op(Kind::Mul, {solver.mkInt(2), x}),
            op(Kind::Add, {op(Kind::Mul, {solver.mkInt(2), y}), solver.mkInt(1)})}),
        op(Kind::Eq, {op(Kind::Mul, {solver.mkInt(4), x}),
            op(Kind::Add, {op(Kind::Mul, {solver.mkInt(4), y}), solver.mkInt(3)})})});
    REQUIRE(static_cast<int>(solver.checkSatAssuming({impossible})) == static_cast<int>(Result::Unsat));
    solver.push();
    solver.assertFormula(impossible);
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
    solver.pop();
    REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("LIA: strict sort - 2x = 1 is unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("LIA: affine lattice repair handles a large-coefficient equality fixed by two inequalities") {
    Solver solver;
    REQUIRE(solver.parseFile(writeTempSmt2(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n"
        "(assert (>= (+ (* 4294967296 x) (* 3123612579 y)) 24))\n"
        "(assert (<= (+ (* 4294967296 x) (* 3123612579 y)) 24))\n"
        "(assert (< y 0))\n(check-sat)\n")));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

TEST_CASE("LIA: basic SAT with branching") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= (* 2 x) 5))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("LIA: disequality with gcd strength") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (= x 0)))\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("LIA: simple bound conflict") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 0))\n"
        "(assert (= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("LIA: branch split round-trip") {
    // This test ensures branch split creates dynamic atoms that are
    // properly registered and asserted on re-solve.
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 2))\n"
        "(assert (>= (* 2 x) 3))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("LIA: model validation passes for integer model") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    ir.registerSort(1, SortKind::Bool);
    ExprId x = ir.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId eq0 = ir.add(TermExpr{Kind::Eq, 1, {x, zero}, {}});

    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class rhs;
    Relation rel;
    REQUIRE(extractLinearConstraint(eq0, ir, coeffs, rhs, rel));
    LinearFormKey lhs;
    for (auto& [n, c] : coeffs) if (c != 0) lhs.terms.push_back({n, c});
    std::sort(lhs.terms.begin(), lhs.terms.end(), [](auto& a, auto& b){ return a.first < b.first; });

    auto sat = createSatSolver();
    Atomizer atomizer(*sat);
    TheoryAtomRegistry registry;
    registry.setContext(sat.get(), &atomizer);

    LiaSolver solver;
    solver.setRegistry(&registry);
    solver.push();
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, eq0, LinearAtomPayload{lhs, rel, RealValue::fromMpq(rhs)}}, true, 0, SatLit{1, true});
    TheoryLemmaDatabase lemmaDb;
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("LIA: model validation fails for fractional integer var") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    ir.registerSort(1, SortKind::Bool);
    ExprId x = ir.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId two = ir.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId le2 = ir.add(TermExpr{Kind::Leq, 1, {x, two}, {}});
    ExprId ge0 = ir.add(TermExpr{Kind::Geq, 1, {x, zero}, {}});

    std::unordered_map<std::string, mpq_class> coeffs1, coeffs2;
    mpq_class rhs1, rhs2;
    Relation rel1, rel2;
    REQUIRE(extractLinearConstraint(le2, ir, coeffs1, rhs1, rel1));
    REQUIRE(extractLinearConstraint(ge0, ir, coeffs2, rhs2, rel2));
    LinearFormKey lhs1, lhs2;
    for (auto& [n, c] : coeffs1) if (c != 0) lhs1.terms.push_back({n, c});
    for (auto& [n, c] : coeffs2) if (c != 0) lhs2.terms.push_back({n, c});
    std::sort(lhs1.terms.begin(), lhs1.terms.end(), [](auto& a, auto& b){ return a.first < b.first; });
    std::sort(lhs2.terms.begin(), lhs2.terms.end(), [](auto& a, auto& b){ return a.first < b.first; });

    auto sat = createSatSolver();
    Atomizer atomizer(*sat);
    TheoryAtomRegistry registry;
    registry.setContext(sat.get(), &atomizer);

    LiaSolver solver;
    solver.setRegistry(&registry);
    solver.push();
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, le2, LinearAtomPayload{lhs1, rel1, RealValue::fromMpq(rhs1)}}, true, 0, SatLit{1, true});
    solver.assertLit(TheoryAtomRecord{2, TheoryId::LIA, false, ge0, LinearAtomPayload{lhs2, rel2, RealValue::fromMpq(rhs2)}}, true, 0, SatLit{2, true});
    TheoryLemmaDatabase lemmaDb;
    auto r = solver.check(lemmaDb);
    CHECK((r.kind == TheoryCheckResult::Kind::Consistent ||
           r.kind == TheoryCheckResult::Kind::Lemma));
}

TEST_CASE("LIA: proveFixedValueByName pins a variable forced through a row") {
    // x = 5 and x + y = 8 jointly force y = 3 via the simplex row, even though
    // no atom directly bounds y. proveFixedValueByName must recover the pin and
    // its reasons (the asserted bound literals). This is the foundation of the
    // NIA Standard-effort linear-prop entailment producer.
    auto sat = createSatSolver();
    Atomizer atomizer(*sat);
    TheoryAtomRegistry registry;
    registry.setContext(sat.get(), &atomizer);

    auto formVar = [](const std::string& n, mpq_class c) {
        LinearFormKey f; f.terms.push_back({n, c}); return f;
    };
    LinearFormKey fxy;
    fxy.terms.push_back({"x", 1});
    fxy.terms.push_back({"y", 1});

    LiaSolver solver;
    solver.setRegistry(&registry);
    solver.push();
    // x = 5  (satVar 1)
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, 100,
        LinearAtomPayload{formVar("x", 1), Relation::Eq, RealValue::fromMpq(5)}},
        true, 0, SatLit{1, true});
    // x + y = 8  (satVar 2)  -> y pinned to 3
    solver.assertLit(TheoryAtomRecord{2, TheoryId::LIA, false, 101,
        LinearAtomPayload{fxy, Relation::Eq, RealValue::fromMpq(8)}},
        true, 0, SatLit{2, true});
    TheoryLemmaDatabase lemmaDb;
    auto r = solver.check(lemmaDb);
    REQUIRE(r.kind == TheoryCheckResult::Kind::Consistent);

    auto px = solver.proveFixedValueByName("x");
    REQUIRE(px.has_value());
    CHECK(px->first == mpq_class(5));

    auto py = solver.proveFixedValueByName("y");
    REQUIRE(py.has_value());
    CHECK(py->first == mpq_class(3));
    // y's pin must be justified by the asserted bound literals (satVars 1/2).
    bool sawReason = false;
    for (const auto& l : py->second) if (l.var == 1 || l.var == 2) sawReason = true;
    CHECK(sawReason);

    CHECK_FALSE(solver.proveFixedValueByName("nonexistent").has_value());

    // Form-level pin: x - y is forced to 5 - 3 = 2.
    LinearFormKey xMinusY;
    xMinusY.terms.push_back({"x", 1});
    xMinusY.terms.push_back({"y", -1});
    auto pf = solver.proveFixedFormValue(xMinusY, mpq_class(0));
    REQUIRE(pf.has_value());
    CHECK(pf->first == mpq_class(2));
}

TEST_CASE("LIA: canonicalizeSign mirrors a negative-leading atom") {
    // y - x <= 0  (form {x:-1,y:1}) canonicalizes to  x - y >= 0.
    LinearFormKey f;
    f.terms.push_back({"x", -1});
    f.terms.push_back({"y", 1});
    Relation rel = Relation::Leq;
    mpq_class rhs = 0;
    bool flipped = LinearConstraintNormalizer::canonicalizeSign(f, rel, rhs);
    CHECK(flipped);
    REQUIRE(f.terms.size() == 2);
    CHECK(f.terms[0].first == "x");
    CHECK(f.terms[0].second == mpq_class(1));
    CHECK(f.terms[1].second == mpq_class(-1));
    CHECK(rel == Relation::Geq);
    // An already-canonical atom is untouched.
    LinearFormKey g;
    g.terms.push_back({"x", 1});
    g.terms.push_back({"y", -1});
    Relation rel2 = Relation::Leq;
    mpq_class rhs2 = 3;
    CHECK_FALSE(LinearConstraintNormalizer::canonicalizeSign(g, rel2, rhs2));
}

TEST_CASE("LIA: proveFixedFormValue pins x-y=0 from x<=y and y<=x (canonical feed)") {
    // The cs_* concurrency pattern: two complementary inequalities over a pair
    // pin the DIFFERENCE to 0 even though neither variable is individually
    // bounded. Sign-canonicalization (the linear-prop feed path) routes both to
    // ONE aux so the bounds collapse to [0,0]. This is the variable-variable
    // equality channel the NIA linear-prop producer needs.
    auto sat = createSatSolver();
    Atomizer atomizer(*sat);
    TheoryAtomRegistry registry;
    registry.setContext(sat.get(), &atomizer);

    LinearFormKey xMinusY; xMinusY.terms.push_back({"x", 1}); xMinusY.terms.push_back({"y", -1});
    LinearFormKey yMinusX; yMinusX.terms.push_back({"x", -1}); yMinusX.terms.push_back({"y", 1});

    LiaSolver solver;
    solver.setRegistry(&registry);
    solver.push();
    {   // x - y <= 0  (already canonical)
        LinearFormKey f = xMinusY; Relation rel = Relation::Leq; mpq_class rhs = 0;
        LinearConstraintNormalizer::canonicalizeSign(f, rel, rhs);
        solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, 200,
            LinearAtomPayload{f, rel, RealValue::fromMpq(rhs)}}, true, 0, SatLit{1, true});
    }
    {   // y - x <= 0  -> canonicalizes to x - y >= 0
        LinearFormKey f = yMinusX; Relation rel = Relation::Leq; mpq_class rhs = 0;
        LinearConstraintNormalizer::canonicalizeSign(f, rel, rhs);
        solver.assertLit(TheoryAtomRecord{2, TheoryId::LIA, false, 201,
            LinearAtomPayload{f, rel, RealValue::fromMpq(rhs)}}, true, 0, SatLit{2, true});
    }
    TheoryLemmaDatabase lemmaDb;
    auto r = solver.check(lemmaDb);
    REQUIRE(r.kind == TheoryCheckResult::Kind::Consistent);

    auto pf = solver.proveFixedFormValue(xMinusY, mpq_class(0));
    REQUIRE(pf.has_value());
    CHECK(pf->first == mpq_class(0));   // x - y pinned to 0
}

namespace {
TheoryAtomRecord replayAtom(SatVar variable, Relation relation, int rhs) {
    LinearFormKey form;
    form.terms.push_back({"incremental-x", 1});
    return TheoryAtomRecord{variable, TheoryId::LIA, false, ExprId(1000 + variable),
        LinearAtomPayload{form, relation, RealValue::fromMpq(rhs)}};
}
void replayAssert(LiaSolver& solver, SatVar variable, Relation relation, int rhs,
                  bool value = true, int level = 0) {
    solver.assertLit(replayAtom(variable, relation, rhs), value, level, SatLit{variable, value});
}
}

TEST_CASE("LIA: append, literal replacement and backtracking preserve current bounds") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    replayAssert(solver, 1, Relation::Geq, 0);
    replayAssert(solver, 2, Relation::Leq, 4);
    for (int i = 0; i < 3; ++i)
        REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    replayAssert(solver, 3, Relation::Geq, 3, true, 1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    replayAssert(solver, 4, Relation::Leq, 3, true, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    auto pin = solver.proveFixedValueByName("incremental-x");
    REQUIRE(pin.has_value());
    CHECK(pin->first == 3);
    solver.backtrackToLevel(1);
    replayAssert(solver, 5, Relation::Geq, 4, true, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    pin = solver.proveFixedValueByName("incremental-x");
    REQUIRE(pin.has_value());
    CHECK(pin->first == 4);
    solver.backtrackToLevel(1);
    replayAssert(solver, 3, Relation::Geq, 3, false, 1);
    replayAssert(solver, 6, Relation::Leq, 1, true, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("LIA: nested scopes restore input trails after checks and conflicts") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    replayAssert(solver, 1, Relation::Geq, 0);
    replayAssert(solver, 2, Relation::Leq, 3);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.push();
    replayAssert(solver, 3, Relation::Geq, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.push();
    replayAssert(solver, 4, Relation::Leq, 1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Conflict);
    solver.push();
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Conflict);
    solver.pop(1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Conflict);
    solver.pop(2);
    replayAssert(solver, 5, Relation::Leq, 1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.reset();
    replayAssert(solver, 6, Relation::Eq, 9);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    const auto pin = solver.proveFixedValueByName("incremental-x");
    REQUIRE(pin.has_value());
    CHECK(pin->first == 9);
}

TEST_CASE("LIA: incremental unary decisions agree with exhaustive finite arithmetic") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    struct Atom { Relation relation; int rhs; bool active = false, value = false; };
    std::vector<Atom> atoms;
    for (int i = 0; i < 8; ++i) atoms.push_back({i % 2 ? Relation::Geq : Relation::Leq, i - 4});
    auto base = [&] { replayAssert(solver, 1, Relation::Geq, -3); replayAssert(solver, 2, Relation::Leq, 3); };
    base();
    for (unsigned step = 0; step < 160; ++step) {
        if (step && step % 17 == 0) {
            solver.backtrackToLevel(0);
            for (auto& a : atoms) a.active = false;
            base();
        }
        const size_t index = (step * 13 + step / 7) % atoms.size();
        auto& a = atoms[index];
        a.active = true;
        a.value = (step / 3) % 2;
        replayAssert(solver, SatVar(10 + index), a.relation, a.rhs, a.value, 1);
        bool exists = false;
        for (int value = -3; value <= 3; ++value) {
            bool valid = true;
            for (const auto& atom : atoms) if (atom.active)
                valid &= (atom.relation == Relation::Leq ? value <= atom.rhs : value >= atom.rhs) == atom.value;
            exists |= valid;
        }
        const auto result = solver.check(db);
        INFO(step);
        CHECK(result.kind == (exists ? TheoryCheckResult::Kind::Consistent : TheoryCheckResult::Kind::Conflict));
        // Rechecking the same context must not retain a rejected local bound.
        CHECK(solver.check(db).kind == result.kind);
    }
}

TEST_CASE("LIA: withdrawing a pin invalidates entailment reads before another check") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    replayAssert(solver, 1, Relation::Geq, 0);
    replayAssert(solver, 2, Relation::Leq, 2);
    replayAssert(solver, 3, Relation::Eq, 1, true, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    REQUIRE(solver.proveFixedValueByName("incremental-x").has_value());
    solver.backtrackToLevel(1);
    CHECK_FALSE(solver.proveFixedValueByName("incremental-x").has_value());
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    CHECK_FALSE(solver.proveFixedValueByName("incremental-x").has_value());
}

TEST_CASE("LIA: positive backtracking retains parent premises before another check") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    replayAssert(solver, 1, Relation::Geq, 9, true, 1);
    replayAssert(solver, 2, Relation::Leq, 9, true, 1);
    replayAssert(solver, 3, Relation::Leq, 10, true, 3);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.backtrackToLevel(1);
    const auto retained = solver.proveFixedValueByName("incremental-x");
    REQUIRE(retained.has_value());
    CHECK(retained->first == 9);
    for (const auto literal : retained->second) CHECK(literal.var != 3);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.backtrackToLevel(1); // a Boolean-only backtrack preserves the same base
    REQUIRE(solver.proveFixedValueByName("incremental-x").has_value());
    CHECK(solver.proveFixedValueByName("incremental-x")->first == 9);
    // An unapplied parent fact must survive a callback that withdraws nothing.
    replayAssert(solver, 4, Relation::Geq, 10, true, 1);
    solver.backtrackToLevel(1);
    CHECK(solver.check(db).kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("LIA: withdrawing multivariable sources preserves disequalities and unordered parent entries") {
    LiaSolver solver;
    TheoryLemmaDatabase db;
    auto source = [&](SatVar var, LinearFormKey lhs, Relation rel, int rhs, int level, bool truth = true) {
        solver.assertLit(TheoryAtomRecord{var, TheoryId::LIA, false, ExprId(2000 + var),
            LinearAtomPayload{std::move(lhs), rel, RealValue::fromMpq(rhs)}}, truth, level, SatLit{var, truth});
    };
    const LinearFormKey x{{{"suffix-x", 1}}}, y{{{"suffix-y", 1}}}, z{{{"suffix-z", 1}}};
    source(1, x, Relation::Eq, 1, 1);
    for (int repeat = 0; repeat < 3; ++repeat) {
        CAPTURE(repeat);
        // Two first occurrences and a repeated term in one source exercise
        // withdrawal/reintroduction of all its original variable columns.
        source(2, {{{"suffix-y", 1}, {"suffix-z", 1}, {"suffix-y", 1}}}, Relation::Eq, 7, 3);
        source(3, y, Relation::Eq, 2, 3);
        source(4, z, Relation::Eq, 3, 3);
        source(5, y, Relation::Eq, repeat % 2 ? 2 : 4, 3, false);
        // Disequality splitting/conflict detection belongs to the model-check
        // effort; propagation may conservatively return Unknown here.
        CHECK(solver.check(db, TheoryEffort::Full).kind == (repeat % 2 ? TheoryCheckResult::Kind::Conflict : TheoryCheckResult::Kind::Consistent));
        solver.backtrackToLevel(1);
        REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
        const auto pin = solver.proveFixedValueByName("suffix-x");
        REQUIRE(pin.has_value());
        CHECK(pin->first == 1);
        for (auto reason : pin->second) CHECK(reason.var == 1);
    }
    // Removing an interior entry must keep the later, lower-level sources.
    source(2, {{{"suffix-y", 1}, {"suffix-z", 1}}}, Relation::Eq, 5, 3);
    source(3, y, Relation::Eq, 2, 2);
    source(4, z, Relation::Eq, 3, 2);
    solver.backtrackToLevel(2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    REQUIRE(solver.proveFixedValueByName("suffix-y").has_value());
    CHECK(solver.proveFixedValueByName("suffix-y")->first == 2);
    // Change an early source's polarity and cache category, then withdraw a
    // suffix. The retained parent disequality is satisfied by the new pin.
    source(1, x, Relation::Eq, 1, 1, false);
    source(6, x, Relation::Eq, 0, 1);
    solver.backtrackToLevel(1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    REQUIRE(solver.proveFixedValueByName("suffix-x").has_value());
    CHECK(solver.proveFixedValueByName("suffix-x")->first == 0);
    solver.push();
    source(7, y, Relation::Eq, 9, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.pop(1);
    source(7, y, Relation::Eq, 8, 2);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.backtrackToLevel(1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    solver.reset();
    source(8, z, Relation::Eq, 6, 1);
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    REQUIRE(solver.proveFixedValueByName("suffix-z").has_value());
    CHECK(solver.proveFixedValueByName("suffix-z")->first == 6);
}

TEST_CASE("LIA: projected disequality guards survive incremental scope changes") {
    Solver solver;
    solver.setLogic("QF_LIA");
    auto op = [&](Kind kind, std::vector<Term> terms) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(terms));
    };
    const auto x = solver.mkConst(solver.intSort(), "projection-x");
    const auto y = solver.mkConst(solver.intSort(), "projection-y");
    const auto z = solver.mkConst(solver.intSort(), "projection-z");
    const auto difference = op(Kind::Sub, {op(Kind::Mul, {solver.mkInt(2), x}), y});
    const auto form = op(Kind::Add, {difference, op(Kind::Mul, {solver.mkInt(512), z})});
    solver.assertFormula(op(Kind::Gt, {form, solver.mkInt(-512)}));
    solver.assertFormula(op(Kind::Lt, {form, solver.mkInt(512)}));
    solver.assertFormula(op(Kind::Not, {op(Kind::Eq, {form, solver.mkInt(0)})}));
    for (int repeat = 0; repeat < 3; ++repeat) {
        solver.push();
        solver.assertFormula(op(Kind::Eq, {difference, solver.mkInt(0)}));
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
        solver.pop();
        solver.push();
        solver.assertFormula(op(Kind::Eq, {difference, solver.mkInt(1)}));
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
        solver.pop();
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
    }
}

namespace {
struct LiaGapContext {
    std::unique_ptr<SatSolver> sat = createSatSolver();
    Atomizer atomizer{*sat};
    TheoryAtomRegistry registry;
    TheoryManager theories;
    TheoryLemmaDatabase lemmas;
    CadicalBackend& backend = dynamic_cast<CadicalBackend&>(*sat);
    CadicalTheoryPropagator propagator{registry, theories, lemmas, backend};
    LiaGapContext() {
        registry.setContext(sat.get(), &atomizer);
        backend.connectPropagator(&propagator);
    }
    ~LiaGapContext() { backend.disconnectPropagator(); }
};
}

TEST_CASE("LIA: fractional disequality gaps use the explained aggregate lattice split") {
    for (bool conditional : {false, true}) {
        for (int sign : {-1, 1}) {
            for (bool fractional : {false, true}) {
                LiaGapContext context;
                auto& registry = context.registry;
                LiaSolver solver;
                solver.setRegistry(&registry);
                LinearFormKey form = conditional
                    ? LinearFormKey{{{"x", 2}, {"y", -1}, {"z", 64}}}
                    : LinearFormKey{{{"x", 64}}};
                const LinearFormKey expectedForm = form;
                const mpq_class offset = conditional ? 5 : 0;
                const mpq_class divisor = fractional ? 3 : 1;
                for (auto& term : form.terms) term.second /= divisor;
                auto assertBound = [&](const LinearFormKey& lhs, Relation relation, const mpq_class& rhs) {
                    const auto literal = registry.getOrCreateLinearBoundAtom(lhs, relation, rhs, TheoryId::LIA);
                    solver.assertLit(*registry.findBySatVar(literal.var), true, 0, literal);
                    return literal;
                };
                std::optional<SatLit> equality;
                if (conditional)
                    equality = assertBound(LinearFormKey{{{"x", 2}, {"y", -1}}}, Relation::Eq, offset);
                // Every feasible LP model lies strictly inside a nonzero lattice
                // gap. Waiting for the disequality's value to be exactly zero
                // misses this stronger explained split and branches on variables.
                assertBound(form, Relation::Geq, mpq_class((offset + (sign > 0 ? mpq_class(1, 4) : mpq_class(-3, 4))) / divisor));
                assertBound(form, Relation::Leq, mpq_class((offset + (sign > 0 ? mpq_class(3, 4) : mpq_class(-1, 4))) / divisor));
                const auto disequality = assertBound(form, Relation::Neq, mpq_class(offset / divisor));
                auto& database = context.lemmas;
                const auto result = solver.check(database, TheoryEffort::Full);
                REQUIRE(result.kind == TheoryCheckResult::Kind::Lemma);
                REQUIRE(result.lemmaOpt.has_value());
                const auto lower = registry.findLinearLiteral(expectedForm, Relation::Leq, mpq_class(offset - 64));
                const auto upper = registry.findLinearLiteral(expectedForm, Relation::Geq, mpq_class(offset + 64));
                REQUIRE(lower.has_value());
                REQUIRE(upper.has_value());
                const auto& clause = result.lemmaOpt->lits;
                CHECK(clause.size() == (conditional ? 4 : 3));
                CHECK(std::find(clause.begin(), clause.end(), disequality.negated()) != clause.end());
                CHECK(std::find(clause.begin(), clause.end(), *lower) != clause.end());
                CHECK(std::find(clause.begin(), clause.end(), *upper) != clause.end());
                if (equality) CHECK(std::find(clause.begin(), clause.end(), equality->negated()) != clause.end());
            }
        }
    }
}


TEST_CASE("LIA: interface disequalities distinguish feasible witnesses from forced equalities") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    auto term = [&](const std::string& name) {
        const auto expr = ir.add({Kind::Variable, 0, {}, Payload(name)});
        const auto id = shared.getOrCreate(expr, 0, name, false);
        shared.addOwner(id, TheoryId::LIA);
        shared.addOwner(id, TheoryId::EUF);
        return id;
    };
    const auto x = term("x"), y = term("y");
    int offset = 1;
    SUBCASE("different offsets admit an exact disequality witness") { offset = 2; }
    SUBCASE("equal offsets still require the complete conflict explanation") { offset = 1; }
    auto define = [&](const std::string& name, int value, SatVar variable) {
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{name, 1}, {"z", -1}}}, Relation::Eq,
                              RealValue::fromInt(value)}},
            true, 1, SatLit::positive(variable));
    };
    define("x", 1, 1);
    define("y", offset, 2);
    solver.assertInterfaceDisequality(x, y, SatLit::positive(3), 1);
    for (const auto effort : {TheoryEffort::Standard, TheoryEffort::Full}) {
        TheoryLemmaDatabase lemmas;
        const auto result = solver.check(lemmas, effort);
        if (offset != 1) {
            CHECK(result.kind == TheoryCheckResult::Kind::Consistent);
            continue;
        }
        REQUIRE(result.kind == TheoryCheckResult::Kind::Conflict);
        REQUIRE(result.conflictOpt.has_value());
        for (SatVar variable : {1, 2, 3}) {
            CHECK(std::find(result.conflictOpt->clause.begin(), result.conflictOpt->clause.end(),
                            SatLit::positive(variable)) != result.conflictOpt->clause.end());
        }
    }
}

TEST_CASE("LIA: shared coordinates keep source names distinct from tableau labels") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    auto term = [&](const std::string& name) {
        const auto expr = ir.add({Kind::Variable, 0, {}, Payload(name)});
        const auto id = shared.getOrCreate(expr, 0, name, false);
        shared.addOwner(id, TheoryId::LIA);
        shared.addOwner(id, TheoryId::EUF);
        return id;
    };
    const auto source = term("s0"), other = term("other");
    auto pin = [&](const std::string& name, int value, SatVar variable) {
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{name, 1}}}, Relation::Eq,
                              RealValue::fromInt(value)}},
            true, 0, SatLit::positive(variable));
    };
    pin("s0", 5, 1);
    int otherValue = 0;
    SUBCASE("different fixed values never imply equality") { otherValue = 0; }
    SUBCASE("equal source values retain their equality") { otherValue = 5; }
    pin("other", otherValue, 2);
    TheoryLemmaDatabase lemmas;
    REQUIRE(solver.check(lemmas, TheoryEffort::Standard).kind ==
            TheoryCheckResult::Kind::Consistent);
    const auto fixed = solver.proveFixedValueByName("s0");
    REQUIRE(fixed);
    CHECK(fixed->first == 5);
    bool found = false;
    for (const auto& equality : solver.getDeducedSharedEqualities()) {
        if (!((equality.a == source && equality.b == other) ||
              (equality.b == source && equality.a == other))) continue;
        found = true;
        CHECK(otherValue == 5);
        CHECK(equality.reasons.size() == 2);
        CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                        SatLit::positive(1)) != equality.reasons.end());
        CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                        SatLit::positive(2)) != equality.reasons.end());
    }
    CHECK(found == (otherValue == 5));
}

TEST_CASE("LIA: shared coordinates observe late variables and withdrawn bounds") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    const auto sourceExpr = ir.add({Kind::Variable, 0, {}, Payload(std::string("s0"))});
    const auto otherExpr = ir.add({Kind::Variable, 0, {}, Payload(std::string("other"))});
    const auto source = shared.getOrCreate(sourceExpr, 0, "s0", false);
    const auto other = shared.getOrCreate(otherExpr, 0, "other", false);
    auto pin = [&](const std::string& name, int value, SatVar variable, int level) {
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{name, 1}}}, Relation::Eq,
                              RealValue::fromInt(value)}},
            true, level, SatLit::positive(variable));
    };
    auto equal = [&] {
        TheoryLemmaDatabase lemmas;
        CHECK(solver.check(lemmas, TheoryEffort::Standard).kind ==
              TheoryCheckResult::Kind::Consistent);
        const auto equalities = solver.getDeducedSharedEqualities();
        return std::any_of(equalities.begin(), equalities.end(), [&](const auto& equality) {
            return (equality.a == source && equality.b == other) ||
                   (equality.a == other && equality.b == source);
        });
    };
    pin("other", 0, 1, 1);
    CHECK_FALSE(equal());
    pin("s0", 5, 2, 2);
    CHECK_FALSE(equal());
    solver.backtrackToLevel(1);
    CHECK_FALSE(equal());
    pin("s0", 0, 3, 2);
    CHECK(equal());
    solver.backtrackToLevel(1);
    CHECK_FALSE(equal());
    pin("s0", 7, 4, 2);
    CHECK_FALSE(equal());
}

#include "search/combination/SharedTermRegistry.h"

TEST_CASE("LIA: shared numeric literals retain their value across source-name collisions") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    auto term = [&](Kind kind, Payload payload, const std::string& name) {
        const auto expr = ir.add({kind, 0, {}, std::move(payload)});
        const auto id = shared.getOrCreate(expr, 0, name, false);
        shared.addOwner(id, TheoryId::LIA);
        shared.addOwner(id, TheoryId::EUF);
        return id;
    };
    const auto zero = term(Kind::ConstInt, Payload(int64_t(0)), "zero");
    const auto source = term(Kind::Variable, Payload(std::string("__const_zero")), "__const_zero");
    const auto other = term(Kind::Variable, Payload(std::string("other")), "other");
    int sourceValue = 5;
    SUBCASE("unequal literal and source values never imply equality") { sourceValue = 5; }
    SUBCASE("equal literal and source values retain their justified equality") { sourceValue = 0; }
    auto pin = [&](const std::string& name, int value, SatVar variable) {
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{name, 1}}}, Relation::Eq,
                              RealValue::fromInt(value)}},
            true, 1, SatLit::positive(variable));
    };
    pin("__const_zero", sourceValue, 1);
    pin("other", 0, 2);
    TheoryLemmaDatabase lemmas;
    REQUIRE(solver.check(lemmas, TheoryEffort::Standard).kind ==
            TheoryCheckResult::Kind::Consistent);
    bool sourceEqual = false, otherEqual = false;
    for (const auto& equality : solver.getDeducedSharedEqualities()) {
        auto pair = [&](SharedTermId a, SharedTermId b) {
            return (equality.a == a && equality.b == b) ||
                   (equality.a == b && equality.b == a);
        };
        if (pair(zero, source)) {
            sourceEqual = true;
            CHECK(sourceValue == 0);
            CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                            SatLit::positive(1)) != equality.reasons.end());
        }
        if (pair(zero, other)) {
            otherEqual = true;
            CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                            SatLit::positive(2)) != equality.reasons.end());
        }
    }
    CHECK(sourceEqual == (sourceValue == 0));
    CHECK(otherEqual);
}

TEST_CASE("Arithmetic shared names follow native expressions across registry reuse") {
    struct NameProbe : LiaSolver {
        using ArithSolverBase::getVarNameForSharedTerm;
    };
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    NameProbe solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    const auto x = ir.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    const auto sx = shared.getOrCreate(x, 0, "display-x", false);
    CHECK(solver.getVarNameForSharedTerm(sx) == "x");
    solver.reset();
    shared.clear();
    const auto zero = ir.add({Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    const auto szero = shared.getOrCreate(zero, 0, "zero", false);
    REQUIRE(szero == sx);
    CHECK(solver.getVarNameForSharedTerm(szero).empty());
    shared.clear();
    const auto y = ir.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
    const auto sy = shared.getOrCreate(y, 0, "display-y", false);
    REQUIRE(sy == sx);
    CHECK(solver.getVarNameForSharedTerm(sy) == "y");
    ir.registerSort(1, SortKind::Bool);
    const auto flag = ir.add({Kind::Variable, 1, {}, Payload(std::string("flag"))});
    const auto sflag = shared.getOrCreate(flag, 1, "display-flag", false);
    CHECK(solver.getVarNameForSharedTerm(sflag).empty());
    NativeTerms replacement;
    replacement.registerSort(0, SortKind::Int);
    const auto z = replacement.add({Kind::Variable, 0, {}, Payload(std::string("z"))});
    REQUIRE(z == x);
    solver.reset();
    ir = std::move(replacement);
    shared.clear();
    shared.setNativeTerms(&ir);
    const auto sz = shared.getOrCreate(z, 0, "display-z", false);
    CHECK(solver.getVarNameForSharedTerm(sz) == "z");
}

TEST_CASE("LIA: shared literals withdraw variable premises across backtracking") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    SharedTermRegistry shared;
    shared.setNativeTerms(&ir);
    LiaSolver solver;
    solver.setNativeTerms(&ir);
    solver.setSharedTermRegistry(&shared);
    auto term = [&](Kind kind, Payload payload, const std::string& name) {
        const auto expr = ir.add({kind, 0, {}, std::move(payload)});
        const auto id = shared.getOrCreate(expr, 0, name, false);
        shared.addOwner(id, TheoryId::LIA);
        shared.addOwner(id, TheoryId::EUF);
        return id;
    };
    const auto zero = term(Kind::ConstInt, Payload(int64_t(0)), "zero");
    const auto source = term(Kind::Variable, Payload(std::string("__const_zero")), "__const_zero");
    const auto anchor = term(Kind::Variable, Payload(std::string("anchor")), "anchor");
    auto pin = [&](const std::string& name, int value, SatVar variable, int level) {
        solver.assertLit({variable, TheoryId::LIA, false, NullExpr,
            LinearAtomPayload{LinearFormKey{{{name, 1}}}, Relation::Eq,
                              RealValue::fromInt(value)}},
            true, level, SatLit::positive(variable));
    };
    auto observe = [&](bool expectedSource) {
        TheoryLemmaDatabase lemmas;
        REQUIRE(solver.check(lemmas, TheoryEffort::Standard).kind ==
                TheoryCheckResult::Kind::Consistent);
        bool sourceEqual = false, anchorEqual = false;
        for (const auto& equality : solver.getDeducedSharedEqualities()) {
            auto pair = [&](SharedTermId a, SharedTermId b) {
                return (equality.a == a && equality.b == b) ||
                       (equality.a == b && equality.b == a);
            };
            if (pair(zero, source)) {
                sourceEqual = true;
                CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                                SatLit::positive(3)) != equality.reasons.end());
                CHECK(std::find(equality.reasons.begin(), equality.reasons.end(),
                                SatLit::positive(2)) == equality.reasons.end());
            }
            if (pair(zero, anchor)) anchorEqual = true;
        }
        CHECK(sourceEqual == expectedSource);
        CHECK(anchorEqual);
    };
    pin("anchor", 0, 1, 1);
    observe(false);
    pin("__const_zero", 5, 2, 2);
    observe(false);
    solver.backtrackToLevel(1);
    observe(false);
    pin("__const_zero", 0, 3, 2);
    observe(true);
    solver.backtrackToLevel(1);
    observe(false);
}
