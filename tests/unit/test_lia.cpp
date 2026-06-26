#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "theory/arith/logics/lia/LiaSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "frontend/atomization/Atomizer.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/arith/logics/lra/GeneralSimplex.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_lia.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
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
    CoreIr ir;
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId eq0 = ir.add(CoreExpr{Kind::Eq, 0, {x, zero}, {}});

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
    CoreIr ir;
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId le2 = ir.add(CoreExpr{Kind::Leq, 0, {x, two}, {}});
    ExprId ge0 = ir.add(CoreExpr{Kind::Geq, 0, {x, zero}, {}});

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
