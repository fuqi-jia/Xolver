#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include "expr/ir.h"
#include "theory/euf/EufSolver.h"
#include "theory/TheoryLemmaDatabase.h"
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_euf.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("EUF: basic equality SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(assert (= a b))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("EUF: direct disequality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(assert (distinct a a))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: eq + distinct UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(assert (= a b))\n"
        "(assert (distinct a b))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: negated equality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(assert (not (= a b)))\n"
        "(assert (= a b))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: congruence UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-fun f (U) U)\n"
        "(assert (= a b))\n"
        "(assert (distinct (f a) (f b)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: nested congruence UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-fun f (U) U)\n"
        "(declare-fun g (U) U)\n"
        "(assert (= a b))\n"
        "(assert (distinct (f (g a)) (f (g b))))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: transitivity + congruence UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-const c U)\n"
        "(declare-fun f (U) U)\n"
        "(assert (= a b))\n"
        "(assert (= b c))\n"
        "(assert (distinct (f a) (f c)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: multi-arg function UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-const c U)\n"
        "(declare-fun f (U U) U)\n"
        "(assert (= a b))\n"
        "(assert (distinct (f a c) (f b c)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: non-injective SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-fun f (U) U)\n"
        "(assert (distinct a b))\n"
        "(assert (= (f a) (f b)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("EUF: Bool predicate UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-fun p (U) Bool)\n"
        "(assert (p a))\n"
        "(assert (not (p a)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool predicate with false UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-fun p (U) Bool)\n"
        "(assert (not (p a)))\n"
        "(assert (p a))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: true != false UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (= p true))\n"
        "(assert (= p false))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool variable UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert p)\n"
        "(assert (not p))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool variable congruence UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert (= p q))\n"
        "(assert p)\n"
        "(assert (not q))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: n-ary equality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-const c U)\n"
        "(assert (= a b c))\n"
        "(assert (distinct a c))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: n-ary distinct UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-const c U)\n"
        "(assert (distinct a b c))\n"
        "(assert (= a c))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: dedup same atom UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(assert (= a b))\n"
        "(assert (not (= b a)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool distinct cardinality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert (distinct p true))\n"
        "(assert (distinct q true))\n"
        "(assert (distinct p q))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool ternary distinct UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(declare-const r Bool)\n"
        "(assert (distinct p q r))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: Bool distinct true SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (distinct p true))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("EUF: cyclic explanation UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-sort U 0)\n"
        "(declare-const a U)\n"
        "(declare-const b U)\n"
        "(declare-const c U)\n"
        "(declare-fun f (U) U)\n"
        "(assert (= a b))\n"
        "(assert (= b c))\n"
        "(assert (= c a))\n"
        "(assert (distinct (f a) (f c)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UF");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("EUF: unsupported mixed logic returns Unknown") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UFLIA)\n"
        "(declare-const a Int)\n"
        "(assert (> a 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_UFLIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unknown));
}

// ---------------------------------------------------------------------------
// Incremental EUF-specific tests (direct EufSolver component tests)
// ---------------------------------------------------------------------------

static TheoryAtomRecord makeEufRecord(ExprId lhs, ExprId rhs,
                                       Relation rel = Relation::Eq,
                                       EufAtomKind kind = EufAtomKind::Equality) {
    return TheoryAtomRecord{SatVar(1), TheoryId::EUF, false, NullExpr,
                            EufAtomPayload{lhs, rhs, rel, kind}};
}

TEST_CASE("EUF incremental: basic equality merge consistent") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: equality then disequality conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(a, b), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: congruence closure conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId f_a = ir.add(CoreExpr{Kind::UFApply, 0, {a}, Payload(std::string("f"))});
    ExprId f_b = ir.add(CoreExpr{Kind::UFApply, 0, {b}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(f_a, f_b), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: nested congruence closure conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId g_a = ir.add(CoreExpr{Kind::UFApply, 0, {a}, Payload(std::string("g"))});
    ExprId g_b = ir.add(CoreExpr{Kind::UFApply, 0, {b}, Payload(std::string("g"))});
    ExprId f_g_a = ir.add(CoreExpr{Kind::UFApply, 0, {g_a}, Payload(std::string("f"))});
    ExprId f_g_b = ir.add(CoreExpr{Kind::UFApply, 0, {g_b}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(f_g_a, f_g_b), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: push pop restores equality class") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.push();
    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.pop(1);
    solver.assertLit(makeEufRecord(a, b), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: push pop removes disequality conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.push();
    solver.assertLit(makeEufRecord(a, b), false, 0, SatLit{2, true});
    auto r1 = solver.check(lemmaDb);
    CHECK(r1.kind == TheoryCheckResult::Kind::Conflict);
    solver.pop(1);
    auto r2 = solver.check(lemmaDb);
    CHECK(r2.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: multiple push pop levels") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId c = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("c"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.push();
    solver.assertLit(makeEufRecord(b, c), true, 0, SatLit{2, true});
    solver.push();
    solver.assertLit(makeEufRecord(a, c), false, 0, SatLit{3, true});
    auto r1 = solver.check(lemmaDb);
    CHECK(r1.kind == TheoryCheckResult::Kind::Conflict);
    solver.pop(1);
    auto r2 = solver.check(lemmaDb);
    CHECK(r2.kind == TheoryCheckResult::Kind::Consistent);
    solver.pop(1);
    auto r3 = solver.check(lemmaDb);
    CHECK(r3.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: backtrack to level 0") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(a, b), false, 1, SatLit{2, true});
    auto r1 = solver.check(lemmaDb);
    CHECK(r1.kind == TheoryCheckResult::Kind::Conflict);
    solver.backtrackToLevel(0);
    auto r2 = solver.check(lemmaDb);
    CHECK(r2.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: Bool true assignment consistent") {
    CoreIr ir;
    ExprId p = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("p"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(p, TrueSentinelExpr, Relation::Eq,
                                    EufAtomKind::BoolTermAsFormula),
                     true, 0, SatLit{1, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: Bool true and false conflict") {
    CoreIr ir;
    ExprId p = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("p"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(p, TrueSentinelExpr, Relation::Eq,
                                    EufAtomKind::BoolTermAsFormula),
                     true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(p, TrueSentinelExpr, Relation::Eq,
                                    EufAtomKind::BoolTermAsFormula),
                     false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: Bool congruence conflict") {
    CoreIr ir;
    ExprId p = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("p"))});
    ExprId q = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("q"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(p, q), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(p, q), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: multi arg congruence conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId c = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("c"))});
    ExprId f_ab = ir.add(CoreExpr{Kind::UFApply, 0, {a, b}, Payload(std::string("f"))});
    ExprId f_cb = ir.add(CoreExpr{Kind::UFApply, 0, {c, b}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, c), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(f_ab, f_cb), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: transitivity congruence conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId c = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("c"))});
    ExprId f_a = ir.add(CoreExpr{Kind::UFApply, 0, {a}, Payload(std::string("f"))});
    ExprId f_c = ir.add(CoreExpr{Kind::UFApply, 0, {c}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(b, c), true, 0, SatLit{2, true});
    solver.assertLit(makeEufRecord(f_a, f_c), false, 0, SatLit{3, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: cyclic explanation conflict") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId c = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("c"))});
    ExprId f_a = ir.add(CoreExpr{Kind::UFApply, 0, {a}, Payload(std::string("f"))});
    ExprId f_c = ir.add(CoreExpr{Kind::UFApply, 0, {c}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    solver.assertLit(makeEufRecord(b, c), true, 0, SatLit{2, true});
    solver.assertLit(makeEufRecord(c, a), true, 0, SatLit{3, true});
    solver.assertLit(makeEufRecord(f_a, f_c), false, 0, SatLit{4, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("EUF incremental: empty push pop consistent") {
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    solver.push();
    solver.pop(1);
    solver.assertLit(makeEufRecord(a, b), false, 0, SatLit{1, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("EUF incremental: late term interning triggers congruence") {
    // Terms f(a) and f(b) are interned lazily when their disequality is
    // asserted, *after* a=b has already been merged. This must still
    // trigger congruence closure.
    CoreIr ir;
    ExprId a = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("b"))});
    ExprId f_a = ir.add(CoreExpr{Kind::UFApply, 0, {a}, Payload(std::string("f"))});
    ExprId f_b = ir.add(CoreExpr{Kind::UFApply, 0, {b}, Payload(std::string("f"))});

    EufSolver solver;
    solver.setCoreIr(&ir);
    TheoryLemmaDatabase lemmaDb;

    // First merge a=b (f terms not yet in egraph)
    solver.assertLit(makeEufRecord(a, b), true, 0, SatLit{1, true});
    // Now assert disequality on f(a) and f(b) -- they get interned here
    solver.assertLit(makeEufRecord(f_a, f_b), false, 0, SatLit{2, true});
    auto r = solver.check(lemmaDb);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}
