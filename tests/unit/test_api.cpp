#include <doctest/doctest.h>
#include <nlcolver/Solver.h>
#include <nlcolver/Result.h>
#include "expr/ir.h"
#include <sstream>
#include <iostream>

using namespace nlcolver;

TEST_CASE("API: sort creation") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort b = s.boolSort();
    Sort i = s.intSort();
    Sort r = s.realSort();

    CHECK(b.id() != NullSort);
    CHECK(i.id() != NullSort);
    CHECK(r.id() != NullSort);
}

TEST_CASE("API: constant terms") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term t = s.mkBool(true);
    Term f = s.mkBool(false);

    CHECK(x.id() != NullExpr);
    CHECK(two.id() != NullExpr);
    CHECK(t.id() != NullExpr);
    CHECK(f.id() != NullExpr);
}

TEST_CASE("API: simple LIA sat") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, two});

    s.assertFormula(le);
    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("API: simple LIA unsat") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term three = s.mkInt(3);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, two});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, three});
    Term andExpr = s.mkOp(static_cast<uint32_t>(Kind::And), {le, ge});

    s.assertFormula(andExpr);
    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("API: simple bool sat") {
    Solver s;

    Sort boolSort = s.boolSort();
    Term p = s.mkBool(true);
    s.assertFormula(p);
    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("API: simple bool unsat") {
    Solver s;

    Sort boolSort = s.boolSort();
    Term p = s.mkBool(true);
    Term notP = s.mkOp(static_cast<uint32_t>(Kind::Not), {p});
    Term andExpr = s.mkOp(static_cast<uint32_t>(Kind::And), {p, notP});

    s.assertFormula(andExpr);
    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("API: dumpSMT2 for API-created problem") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, two});
    s.assertFormula(le);

    std::ostringstream oss;
    s.dumpSMT2(oss);
    std::string output = oss.str();
    CHECK(output.find("(<= x 2)") != std::string::npos);
}

TEST_CASE("API: checkSatAssuming") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term three = s.mkInt(3);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, two});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, three});

    s.assertFormula(le);
    Result r1 = s.checkSatAssuming({ge});
    CHECK(static_cast<int>(r1) == static_cast<int>(Result::Unsat));

    Result r2 = s.checkSat();
    CHECK(static_cast<int>(r2) == static_cast<int>(Result::Sat));
}

TEST_CASE("API: getModel for LIA") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term zero = s.mkInt(0);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, zero});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, zero});

    s.assertFormula(le);
    s.assertFormula(ge);

    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));

    Model m = s.getModel();
    const std::string* val = m.getValue(x.id());
    CHECK(val != nullptr);
    CHECK(*val == "0");
}

TEST_CASE("API: getModel for NRA algebraic root") {
    Solver s;
    s.setLogic("QF_NRA");

    Sort realSort = s.realSort();
    Term x = s.mkConst(realSort, "x");
    Term two = s.mkReal("2");
    Term zero = s.mkReal("0");
    Term x2 = s.mkOp(static_cast<uint32_t>(Kind::Mul), {x, x});
    Term eq = s.mkOp(static_cast<uint32_t>(Kind::Eq), {x2, two});
    Term gt = s.mkOp(static_cast<uint32_t>(Kind::Gt), {x, zero});

    s.assertFormula(eq);
    s.assertFormula(gt);

    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));

    Model m = s.getModel();
    const std::string* val = m.getValue(x.id());
    CHECK(val != nullptr);
    // Should be (AlgebraicNumber (poly 1 0 -2) (lower ...) (upper ...))
    CHECK(val->find("(AlgebraicNumber (poly") != std::string::npos);
}

TEST_CASE("API: getModel for NIA") {
    Solver s;
    s.setLogic("QF_NIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term x2 = s.mkOp(static_cast<uint32_t>(Kind::Mul), {x, x});
    Term eq = s.mkOp(static_cast<uint32_t>(Kind::Eq), {x2, two});

    // x^2 = 2 has no integer solutions -> unsat
    s.assertFormula(eq);
    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("API: getValue for LIA") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term five = s.mkInt(5);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, five});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, five});

    s.assertFormula(le);
    s.assertFormula(ge);

    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));

    Term val = s.getValue(x);
    CHECK(!val.isNull());
    // val should be a fresh ConstInt term representing 5
    // (not necessarily the same ExprId as 'five' since getValue creates a new term)
}

TEST_CASE("API: getModel for NRA") {
    Solver s;
    s.setLogic("QF_NRA");

    Sort realSort = s.realSort();
    Term x = s.mkConst(realSort, "x");
    Term zero = s.mkReal("0");
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, zero});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, zero});

    s.assertFormula(le);
    s.assertFormula(ge);

    Result r = s.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));

    Model m = s.getModel();
    const std::string* val = m.getValue(x.id());
    CHECK(val != nullptr);
    CHECK(*val == "0");
}

TEST_CASE("API: getUnsatCore for checkSatAssuming") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term two = s.mkInt(2);
    Term three = s.mkInt(3);
    Term le = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, two});
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, three});

    s.assertFormula(le);
    Result r = s.checkSatAssuming({ge});
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));

    auto core = s.getUnsatCore();
    CHECK(!core.empty());
    CHECK(core[0] == ge);
}
