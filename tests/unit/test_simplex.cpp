#include <doctest/doctest.h>
#include "theory/arith/lra/LraSolver.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "expr/ir.h"
#include <random>

using namespace zolver;

static TheoryAtomRecord makeLinearAtom(SatVar sv, ExprId eid, const CoreIr& ir, TheoryId theory) {
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class rhs;
    Relation rel;
    REQUIRE(extractLinearConstraint(eid, ir, coeffs, rhs, rel));
    LinearFormKey lhs;
    for (auto& [n, c] : coeffs) {
        if (c != 0) lhs.terms.push_back({n, c});
    }
    std::sort(lhs.terms.begin(), lhs.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });
    return TheoryAtomRecord{sv, theory, false, eid, LinearAtomPayload{lhs, rel, RealValue::fromMpq(rhs)}};
}

TEST_CASE("LraSolver: single variable bound conflict") {
    CoreIr ir;

    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId lt0 = ir.add(CoreExpr{Kind::Lt, 0, {x, zero}, {}});

    ExprId eq0 = ir.add(CoreExpr{Kind::Eq, 0, {x, zero}, {}});

    LraSolver solver;
    solver.push();

    TheoryLemmaDatabase lemmaDb;

    // assert x < 0 (satVar 1)
    solver.assertLit(makeLinearAtom(1, lt0, ir, TheoryId::LRA), true, 0, SatLit{1, true});
    auto r1 = solver.check(lemmaDb);
    CHECK(r1.kind == TheoryCheckResult::Kind::Consistent);

    // assert x = 0 (satVar 2)
    solver.assertLit(makeLinearAtom(2, eq0, ir, TheoryId::LRA), true, 0, SatLit{2, true});
    auto r2 = solver.check(lemmaDb);
    CHECK(r2.kind == TheoryCheckResult::Kind::Conflict);

    CHECK(r2.conflictOpt.has_value());
    CHECK(r2.conflictOpt->clause.size() == 2);
}

TEST_CASE("GeneralSimplex: addConstraint semantic contract") {
    GeneralSimplex gs;

    int x = gs.addVar("x");
    int y = gs.addVar("y");

    // addConstraint({x:1, y:2}, 3) creates s = x + 2y - 3
    int s = gs.addConstraint({{x, 1}, {y, 2}}, 3);

    // Assert s = 0 (which means x + 2y = 3)
    gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(1), true}));
    gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(1), true}));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    auto valX = gs.value(x);
    auto valY = gs.value(y);
    auto valS = gs.value(s);

    // s should be exactly 0
    CHECK(valS.isZero());

    // x + 2y should equal 3
    CHECK(valX + mpq_class(2) * valY == DeltaRational(3));

    CHECK(gs.debugCheckInvariants());
}

TEST_CASE("GeneralSimplex: sparse stress test (sat)") {
    GeneralSimplex gs;

    // Create 10 variables
    std::vector<int> vars;
    for (int i = 0; i < 10; ++i) {
        vars.push_back(gs.addVar("x" + std::to_string(i)));
    }

    // Add 5 sparse constraints, each involving only 2-3 variables
    // Constraint 0: x0 + x1 = 5
    int s0 = gs.addConstraint({{vars[0], 1}, {vars[1], 1}}, 5);
    // Constraint 1: x1 + x2 = 3
    int s1 = gs.addConstraint({{vars[1], 1}, {vars[2], 1}}, 3);
    // Constraint 2: x3 - x4 = 0
    int s2 = gs.addConstraint({{vars[3], 1}, {vars[4], -1}}, 0);
    // Constraint 3: x5 + 2*x6 = 10
    int s3 = gs.addConstraint({{vars[5], 1}, {vars[6], 2}}, 10);
    // Constraint 4: x7 - x8 + x9 = 1
    int s4 = gs.addConstraint({{vars[7], 1}, {vars[8], -1}, {vars[9], 1}}, 1);

    // Assert all equalities (s_i = 0)
    for (int i = 0; i < 5; ++i) {
        int s = (i == 0) ? s0 : (i == 1) ? s1 : (i == 2) ? s2 : (i == 3) ? s3 : s4;
        gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(i * 2 + 1), true}));
        gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(i * 2 + 2), true}));
    }

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Sat);

    auto v0 = gs.value(vars[0]);
    auto v1 = gs.value(vars[1]);
    auto v2 = gs.value(vars[2]);
    auto v3 = gs.value(vars[3]);
    auto v4 = gs.value(vars[4]);
    auto v5 = gs.value(vars[5]);
    auto v6 = gs.value(vars[6]);
    auto v7 = gs.value(vars[7]);
    auto v8 = gs.value(vars[8]);
    auto v9 = gs.value(vars[9]);

    CHECK(v0 + v1 == DeltaRational(5));
    CHECK(v1 + v2 == DeltaRational(3));
    CHECK(v3 - v4 == DeltaRational(0));
    CHECK(v5 + mpq_class(2) * v6 == DeltaRational(10));
    CHECK(v7 - v8 + v9 == DeltaRational(1));

    CHECK(gs.debugCheckInvariants());
}

TEST_CASE("GeneralSimplex: sparse stress test (unsat)") {
    GeneralSimplex gs;

    int x = gs.addVar("x");

    // x <= 1  and  x >= 3  => unsat
    int s0 = gs.addConstraint({{x, 1}}, 1);   // s0 = x - 1
    int s1 = gs.addConstraint({{x, 1}}, 3);   // s1 = x - 3

    // s0 <= 0  (x <= 1)
    gs.assertUpper(s0, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(1), true}));
    // s1 >= 0  (x >= 3)
    gs.assertLower(s1, BoundInfo(BoundValue(DeltaRational(0)), SatLit{static_cast<SatVar>(2), true}));

    auto r = gs.check();
    CHECK(r == GeneralSimplex::Result::Unsat);

    CHECK(gs.debugCheckInvariants());
}

TEST_CASE("GeneralSimplex: randomized sparse LRA stress") {
    std::mt19937 rng(42);
    std::uniform_int_distribution<int> numVarsDist(5, 15);
    std::uniform_int_distribution<int> numConsDist(3, 8);
    std::uniform_int_distribution<int> coeffDist(-5, 5);
    std::uniform_int_distribution<int> rhsDist(-10, 10);
    std::uniform_int_distribution<int> numBoundsDist(1, 4);
    std::uniform_real_distribution<double> boundValueDist(-10.0, 10.0);

    for (int trial = 0; trial < 50; ++trial) {
        GeneralSimplex gs;

        int n = numVarsDist(rng);
        int m = numConsDist(rng);

        std::vector<int> vars;
        for (int i = 0; i < n; ++i) {
            vars.push_back(gs.addVar("x" + std::to_string(i)));
        }

        // Add sparse constraints (each involves 1-3 vars)
        std::vector<int> auxVars;
        for (int c = 0; c < m; ++c) {
            std::vector<std::pair<int, mpq_class>> terms;
            int nTerms = 1 + (rng() % 3);
            for (int t = 0; t < nTerms; ++t) {
                int v = vars[rng() % n];
                int coeff = coeffDist(rng);
                if (coeff != 0) terms.push_back({v, coeff});
            }
            if (terms.empty()) continue;
            int rhs = rhsDist(rng);
            int s = gs.addConstraint(terms, rhs);
            auxVars.push_back(s);
        }

        if (auxVars.empty()) continue;

        // Assert some random bounds
        int nb = numBoundsDist(rng);
        for (int b = 0; b < nb; ++b) {
            int s = auxVars[rng() % auxVars.size()];
            double val = boundValueDist(rng);
            mpq_class q(val);
            bool isLower = (rng() % 2) == 0;
            if (isLower) {
                gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(q)), SatLit{static_cast<SatVar>(b + 1), true}));
            } else {
                gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(q)), SatLit{static_cast<SatVar>(b + 1), true}));
            }
        }

        auto r = gs.check();
        CHECK((r == GeneralSimplex::Result::Sat || r == GeneralSimplex::Result::Unsat));
        CHECK(gs.debugCheckInvariants());
    }
}
