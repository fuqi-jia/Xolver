#include <doctest/doctest.h>
#include <xolver/Solver.h>
#include <xolver/Result.h>
#include "expr/ir.h"
#include <sstream>
#include <iostream>

using namespace xolver;

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

TEST_CASE("API: nonlinear div/mod on pure Int never false-SATs (soft_float floor)") {
    // (> x 0) AND (mod (* x x) x) = 5.  x*x is divisible by x, so the mod is 0
    // for x>0 and = 5 is unsat (z3 agrees). Our nonlinear mod reasoning is
    // incomplete and floors to unknown here. The soundness floor for the
    // soft_float class (incomplete nonlinear div/mod) is: NEVER fabricate sat.
    // Assert != Sat so a future regression is caught whether we floor to unknown
    // (today) or strengthen to a proved unsat -- only a false-SAT fails.
    Solver s;
    s.setLogic("QF_NIA");
    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term xx = s.mkOp(static_cast<uint32_t>(Kind::Mul), {x, x});
    Term m = s.mkOp(static_cast<uint32_t>(Kind::Mod), {xx, x});
    Term eq5 = s.mkOp(static_cast<uint32_t>(Kind::Eq), {m, s.mkInt(5)});
    Term gt0 = s.mkOp(static_cast<uint32_t>(Kind::Gt), {x, s.mkInt(0)});
    s.assertFormula(eq5);
    s.assertFormula(gt0);
    Result r = s.checkSat();
    // unsat (correct) or unknown (sound floor) are both fine; sat would be unsound.
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Sat));
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

TEST_CASE("API: getUnsatCore minimizes to the conflicting subset") {
    Solver s;
    s.setLogic("QF_LIA");

    Sort intSort = s.intSort();
    Term x = s.mkConst(intSort, "x");
    Term le2  = s.mkOp(static_cast<uint32_t>(Kind::Leq), {x, s.mkInt(2)});   // x <= 2  (HARD)
    Term ge10 = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, s.mkInt(10)});  // x >= 10 (assumption, conflicts le2)
    Term ge0  = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, s.mkInt(0)});   // x >= 0  (assumption, irrelevant)

    // Hard le2 alone is SAT; adding ge10 makes it UNSAT, adding ge0 does not.
    // So any SOUND core must contain ge10, and a MINIMIZED one drops ge0.
    s.assertFormula(le2);
    Result r = s.checkSatAssuming({ge0, ge10});
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));

    auto core = s.getUnsatCore();
    bool hasGe10 = false, hasGe0 = false;
    for (const auto& t : core) {
        if (t == ge10) hasGe10 = true;
        if (t == ge0)  hasGe0 = true;
    }
    // Soundness invariant (ge10 is the only assumption that creates the conflict):
    CHECK(hasGe10);
    // Minimization (the win over the old return-all-assumptions stub):
    CHECK(core.size() < 2);
    CHECK_FALSE(hasGe0);
}

// Deep-recursion regression for the global recursion->iteration sweep. These run
// on the default (8MB) test-thread stack: a still-recursive frontend/theory
// walker overflows here. The deep ARITH term exercises PolynomialConverter::
// collectRec + LogicFeatureDetector::scanExpr; the deep BOOLEAN nesting
// exercises Atomizer::atomizeRec's pre-pass. Both must answer, not crash.
TEST_CASE("API: deep arithmetic term does not overflow (collectRec/scanExpr)") {
    constexpr int kDeep = 60000;
    Solver s;
    s.setLogic("QF_LIA");
    Sort i = s.intSort();
    Term x = s.mkConst(i, "x");
    Term chain = x;
    for (int k = 0; k < kDeep; ++k) {
        chain = s.mkOp(static_cast<uint32_t>(Kind::Add), {chain, x});  // ((x+x)+x)+...
    }
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {chain, s.mkInt(0)});
    s.assertFormula(ge);
    Result r = s.checkSat();  // N*x >= 0 is sat (x=0); must not segfault
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("API: deep boolean nesting does not overflow (atomizeRec)") {
    constexpr int kDeep = 60000;
    Solver s;
    s.setLogic("QF_LIA");
    Sort i = s.intSort();
    Term x = s.mkConst(i, "x");
    Term atom = s.mkOp(static_cast<uint32_t>(Kind::Geq), {x, s.mkInt(0)});
    Term chain = atom;
    for (int k = 0; k < kDeep; ++k) {
        chain = s.mkOp(static_cast<uint32_t>(Kind::Or), {chain, atom});  // (or A (or A ...))
    }
    s.assertFormula(chain);
    Result r = s.checkSat();  // sat (x=0); must not segfault during atomization
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("API: deep nonlinear real term does not overflow (NRA path + validator)") {
    // Deep nested sum of x*x in QF_NRA: exercises PolynomialConverter::collectRec,
    // extractLinearExpr's nonlinear-reject, and ArithModelValidator::eval on the
    // deep assertion during SAT model validation. N*x^2 >= 0 is sat (x=0).
    constexpr int kDeep = 30000;
    Solver s;
    s.setLogic("QF_NRA");
    Sort rs = s.realSort();
    Term x = s.mkConst(rs, "x");
    Term sq = s.mkOp(static_cast<uint32_t>(Kind::Mul), {x, x});
    Term chain = sq;
    for (int k = 0; k < kDeep; ++k) {
        chain = s.mkOp(static_cast<uint32_t>(Kind::Add), {chain, sq});
    }
    Term ge = s.mkOp(static_cast<uint32_t>(Kind::Geq), {chain, s.mkReal("0")});
    s.assertFormula(ge);
    Result r = s.checkSat();  // must not segfault in collectRec/NRA/ArithModelValidator
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
