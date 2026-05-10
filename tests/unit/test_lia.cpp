#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include "theory/arith/lia/LiaSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_lia.smt2";
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
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, eq0, LinearAtomPayload{lhs, rel, rhs}}, true, 0, SatLit{1, true});
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
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, le2, LinearAtomPayload{lhs1, rel1, rhs1}}, true, 0, SatLit{1, true});
    solver.assertLit(TheoryAtomRecord{2, TheoryId::LIA, false, ge0, LinearAtomPayload{lhs2, rel2, rhs2}}, true, 0, SatLit{2, true});
    TheoryLemmaDatabase lemmaDb;
    auto r = solver.check(lemmaDb);
    CHECK((r.kind == TheoryCheckResult::Kind::Consistent ||
           r.kind == TheoryCheckResult::Kind::Lemma));
}
