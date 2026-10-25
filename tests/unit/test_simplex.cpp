#include <doctest/doctest.h>
#include "applications/smt/qflra/LraSolver.h"
#include "search/lra/GeneralSimplex.h"
#include "algebra/linear/LinearExpr.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "ir/NativeTerms.h"
#include <random>
#include <stdexcept>
#include <array>

using namespace xolver;

TEST_CASE("GeneralSimplex: pop restores parent conflict state and permits the next branch") {
    GeneralSimplex simplex;
    const auto x = simplex.addVar("x");
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
    REQUIRE((simplex.check() == GeneralSimplex::Result::Sat));
    simplex.push();
    CHECK_FALSE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(-1)), SatLit::positive(2))));
    REQUIRE((simplex.check() == GeneralSimplex::Result::Unsat));
    const auto conflict = simplex.getConflict();
    simplex.push();
    simplex.pop();
    REQUIRE((simplex.check() == GeneralSimplex::Result::Unsat));
    REQUIRE(simplex.getConflict().size() == conflict.size());
    for (std::size_t i = 0; i < conflict.size(); ++i)
        CHECK(simplex.getConflict()[i].reason == conflict[i].reason);
    simplex.pop();
    CHECK(simplex.getConflict().empty());
    REQUIRE((simplex.check() == GeneralSimplex::Result::Sat));
    simplex.push();
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(1)), SatLit::positive(3))));
    REQUIRE((simplex.check() == GeneralSimplex::Result::Sat));
    CHECK(simplex.value(x).a >= 1);
    simplex.pop();
    CHECK((simplex.check() == GeneralSimplex::Result::Sat));
}

static TheoryAtomRecord makeLinearAtom(SatVar sv, ExprId eid, const NativeTerms& ir, TheoryId theory) {
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
    NativeTerms ir;
    ir.registerSort(0, SortKind::Real);
    ir.registerSort(1, SortKind::Bool);

    ExprId x = ir.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(TermExpr{Kind::ConstReal, 0, {}, Payload(int64_t(0))});
    ExprId lt0 = ir.add(TermExpr{Kind::Lt, 1, {x, zero}, {}});

    ExprId eq0 = ir.add(TermExpr{Kind::Eq, 1, {x, zero}, {}});

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

TEST_CASE("GeneralSimplex: fixed-value closure shares diamond dependencies and retains premises") {
    GeneralSimplex gs;
    const int x = gs.addVar("x"), y = gs.addVar("y"), z = gs.addVar("z"), w = gs.addVar("w");
    const int xy = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    const int xz = gs.addConstraint({{x, 1}, {z, 1}}, 7);
    const int yzw = gs.addConstraint({{y, 1}, {z, 1}, {w, 1}}, 11);
    SatVar reason = 1;
    auto pin = [&](int var, int value) {
        REQUIRE(gs.assertLower(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason++))));
        REQUIRE(gs.assertUpper(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason++))));
    };
    pin(x, 2); pin(xy, 0); pin(xz, 0); pin(yzw, 0);
    for (int pass = 0; pass < 2; ++pass) {
        if (pass) REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
        const auto analysis = gs.analyzeFixedValues();
        const auto proof = analysis.prove(w);
        REQUIRE(proof.has_value());
        CHECK(proof->first == DeltaRational(3));
        CHECK(proof->second.size() == 8);
        // Replay only the returned bound premises on an independent finite
        // assignment grid. Auxiliary values use the original row equations.
        unsigned witnesses = 0;
        for (int a = 0; a <= 6; ++a) for (int b = 0; b <= 6; ++b)
            for (int c = 0; c <= 6; ++c) for (int d = 0; d <= 6; ++d) {
                const std::vector<int> values{a, b, c, d, a+b-5, a+c-7, b+c+d-11};
                bool premises = true;
                for (const auto& br : proof->second) {
                    const auto state = gs.varState(br.var);
                    const auto actual = DeltaRational(values.at(br.var));
                    premises &= br.isLower ? actual >= state.lower.bound.value
                                           : actual <= state.upper.bound.value;
                }
                if (premises) { ++witnesses; CHECK(DeltaRational(d) == proof->first); }
            }
        CHECK(witnesses == 1);
    }
}

TEST_CASE("GeneralSimplex: fixed-value analysis respects cycles, strict values and backtracking") {
    GeneralSimplex gs;
    const int x = gs.addVar("x"), y = gs.addVar("y");
    const int equality = gs.addConstraint({{x, 2}, {y, -3}}, 1);
    REQUIRE(gs.assertLower(equality, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
    REQUIRE(gs.assertUpper(equality, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(2))));
    CHECK_FALSE(gs.analyzeFixedValues().prove(x));
    CHECK_FALSE(gs.analyzeFixedValues().prove(y));
    CHECK_FALSE(gs.proveFixedValue(-1));
    gs.push();
    const DeltaRational pinned(mpq_class(1, 2), mpq_class(3, 5));
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(pinned), SatLit::positive(3)), 1));
    REQUIRE(gs.assertUpper(x, BoundInfo(BoundValue(pinned), SatLit::positive(4)), 1));
    const auto proof = gs.analyzeFixedValues().prove(y);
    REQUIRE(proof.has_value());
    CHECK(proof->first == DeltaRational(mpq_class(0), mpq_class(2, 5)));
    CHECK(proof->second.size() == 4);
    gs.pop();
    CHECK_FALSE(gs.analyzeFixedValues().prove(x));
    CHECK_FALSE(gs.analyzeFixedValues().prove(y));
}

TEST_CASE("GeneralSimplex: fixed-value proofs replay against independent small linear systems") {
    std::mt19937 random(20261025);
    for (int sample = 0; sample < 32; ++sample) {
        GeneralSimplex gs;
        std::array<int, 3> variables;
        std::array<int, 3> witness;
        for (int i = 0; i < 3; ++i) {
            variables[i] = gs.addVar("replay-" + std::to_string(i));
            witness[i] = static_cast<int>(random() % 5) - 2;
        }
        struct Equation { int aux; std::array<int, 3> coefficients; int rhs; };
        std::vector<Equation> equations;
        for (int row = 0; row < 3; ++row) {
            std::array<int, 3> coefficients;
            std::vector<std::pair<int, mpq_class>> terms;
            for (int i = 0; i < 3; ++i) {
                coefficients[i] = static_cast<int>(random() % 7) - 3;
                if (coefficients[i]) terms.push_back({variables[i], coefficients[i]});
            }
            const int rhs = static_cast<int>(random() % 7) - 3;
            equations.push_back({gs.addConstraint(terms, rhs), coefficients, rhs});
        }
        const int constant = gs.addConstraint({}, -2);
        auto evaluate = [&](const std::array<int, 3>& point) {
            std::vector<int> values(gs.numVars());
            for (int i = 0; i < 3; ++i) values[variables[i]] = point[i];
            for (const auto& equation : equations) {
                int value = -equation.rhs;
                for (int i = 0; i < 3; ++i) value += equation.coefficients[i] * point[i];
                values[equation.aux] = value;
            }
            values[constant] = 2;
            return values;
        };
        const auto values = evaluate(witness);
        SatVar reason = 1;
        for (int var = 0; var < constant; ++var) {
            if (random() % 3) continue;
            REQUIRE(gs.assertLower(var, BoundInfo(BoundValue(DeltaRational(values[var])), SatLit::positive(reason++))));
            REQUIRE(gs.assertUpper(var, BoundInfo(BoundValue(DeltaRational(values[var])), SatLit::positive(reason++))));
        }
        for (int pass = 0; pass < 2; ++pass) {
            if (pass) REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
            const auto analysis = gs.analyzeFixedValues();
            REQUIRE(analysis.prove(constant));
            CHECK(analysis.prove(constant)->first == DeltaRational(2));
            for (int target = 0; target < gs.numVars(); ++target) {
                CAPTURE(sample);
                CAPTURE(pass);
                CAPTURE(target);
                const auto proof = analysis.prove(target);
                if (!proof) continue;
                unsigned models = 0;
                for (int a = -2; a <= 2; ++a) for (int b = -2; b <= 2; ++b)
                    for (int c = -2; c <= 2; ++c) {
                        const auto actual = evaluate({a, b, c});
                        bool premises = true;
                        for (const auto& premise : proof->second) {
                            const auto state = gs.varState(premise.var);
                            const DeltaRational value(actual.at(premise.var));
                            premises &= premise.isLower ? value >= state.lower.bound.value
                                                       : value <= state.upper.bound.value;
                        }
                        if (premises) {
                            ++models;
                            CHECK(DeltaRational(actual[target]) == proof->first);
                        }
                    }
                CHECK(models > 0);
            }
        }
    }
}

TEST_CASE("GeneralSimplex: fixed-value proof chains use iterative shared dependencies") {
    GeneralSimplex gs;
    constexpr int depth = 2048;
    int variable = gs.addVar("root");
    SatVar reason = 1;
    auto pin = [&](int var, int value) {
        REQUIRE(gs.assertLower(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason++))));
        REQUIRE(gs.assertUpper(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason++))));
    };
    pin(variable, 1);
    for (int i = 0; i < depth; ++i) {
        const int next = gs.addVar("chain-" + std::to_string(i));
        pin(gs.addConstraint({{variable, 1}, {next, 1}}, 0), 0);
        variable = next;
    }
    const auto proof = gs.analyzeFixedValues().prove(variable);
    REQUIRE(proof.has_value());
    CHECK(proof->first == DeltaRational(1));
    CHECK(proof->second.size() == 2 * (depth + 1));
}

TEST_CASE("GeneralSimplex: shared fixed-value snapshots follow bounds, pivots and new definitions") {
    GeneralSimplex gs;
    const int x = gs.addVar("snapshot-x"), y = gs.addVar("snapshot-y");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    auto pin = [&](int var, int value, SatVar reason) {
        REQUIRE(gs.assertLower(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason))));
        REQUIRE(gs.assertUpper(var, BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason + 1))));
    };
    pin(x, 2, 1); pin(sum, 0, 3);
    const auto before = gs.sharedFixedValueAnalysis();
    const auto beforeRevision = gs.analysisRevision();
    const auto boundRevision = gs.boundRevision();
    REQUIRE(before->fixedValue(y));
    CHECK(*before->fixedValue(y) == DeltaRational(3));
    CHECK(gs.sharedFixedValueAnalysis() == before);
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(1)), SatLit::positive(99))));
    CHECK(gs.sharedFixedValueAnalysis() == before); // redundant assertion changes no premise
    CHECK(gs.analysisRevision() == beforeRevision);
    CHECK_FALSE(gs.isBasic(y));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.isBasic(y));
    const auto pivoted = gs.sharedFixedValueAnalysis();
    CHECK(pivoted != before);
    CHECK(gs.analysisRevision() != beforeRevision);
    CHECK(gs.boundRevision() == boundRevision);
    REQUIRE(pivoted->prove(y));
    CHECK(pivoted->prove(y)->first == DeltaRational(3));
    CHECK(*before->fixedValue(y) == DeltaRational(3)); // outstanding handle stays immutable

    gs.push();
    CHECK_FALSE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(4)), SatLit::positive(10)), 1));
    const auto conflicting = gs.sharedFixedValueAnalysis();
    CHECK(conflicting != pivoted);
    gs.pop();
    CHECK(gs.sharedFixedValueAnalysis() != conflicting);
    gs.resetActiveBounds();
    CHECK_FALSE(gs.sharedFixedValueAnalysis()->fixedValue(y));
    pin(x, 5, 11); pin(sum, 0, 13);
    REQUIRE(gs.proveFixedValue(y));
    CHECK(gs.proveFixedValue(y)->first == DeltaRational(0));

    const auto old = gs.sharedFixedValueAnalysis();
    const int z = gs.addVar("snapshot-z");
    CHECK(gs.sharedFixedValueAnalysis() != old);
    CHECK_FALSE(gs.sharedFixedValueAnalysis()->fixedValue(z));
    const int difference = gs.addConstraint({{y, 1}, {z, -1}}, 1);
    pin(difference, 0, 15);
    REQUIRE(gs.proveFixedValue(z));
    CHECK(gs.proveFixedValue(z)->first == DeltaRational(-1));
    CHECK_FALSE(old->fixedValue(z));
}

TEST_CASE("GeneralSimplex: cached fixed values cannot leak through scope removal, copies or reset") {
    GeneralSimplex gs;
    const int x = gs.addVar("scope-x");
    gs.push();
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(7)), SatLit::positive(1)), 1));
    REQUIRE(gs.assertUpper(x, BoundInfo(BoundValue(DeltaRational(7)), SatLit::positive(2)), 1));
    const auto pinned = gs.sharedFixedValueAnalysis();
    REQUIRE(pinned->prove(x));
    GeneralSimplex copy = gs;
    copy.resetActiveBounds();
    CHECK_FALSE(copy.proveFixedValue(x));
    CHECK(gs.sharedFixedValueAnalysis() == pinned);
    gs.pop();
    CHECK_FALSE(gs.proveFixedValue(x));
    CHECK(pinned->prove(x)->first == DeltaRational(7));
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(9)), SatLit::positive(3)), 2));
    REQUIRE(gs.assertUpper(x, BoundInfo(BoundValue(DeltaRational(9)), SatLit::positive(4)), 2));
    REQUIRE(gs.proveFixedValue(x));
    CHECK(gs.proveFixedValue(x)->first == DeltaRational(9));
    gs.backtrackToLevel(0);
    CHECK_FALSE(gs.proveFixedValue(x));
    gs.reset();
    CHECK(gs.addVar("reused-index") == x);
    CHECK_FALSE(gs.proveFixedValue(x));
    CHECK_FALSE(gs.sharedFixedValueAnalysis()->fixedValue(-1));
    CHECK_FALSE(gs.sharedFixedValueAnalysis()->fixedValue(100));
}

TEST_CASE("GeneralSimplex: non-pinning tightenings retain valid fixed-value proofs") {
    GeneralSimplex gs;
    const int x = gs.addVar("tightening-x"), y = gs.addVar("tightening-y");
    const int z = gs.addVar("tightening-z");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    auto endpoint = [](int value, int reason) {
        return BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason));
    };
    REQUIRE(gs.assertLower(x, endpoint(2, 1)));
    REQUIRE(gs.assertUpper(x, endpoint(2, 2)));
    REQUIRE(gs.assertLower(sum, endpoint(0, 3)));
    REQUIRE(gs.assertUpper(sum, endpoint(0, 4)));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    const auto pinned = gs.sharedFixedValueAnalysis();
    REQUIRE(pinned->prove(y));
    CHECK(pinned->prove(y)->first == DeltaRational(3));
    auto revision = gs.boundRevision();
    REQUIRE(gs.assertLower(z, endpoint(0, 5)));
    CHECK(gs.boundRevision() != revision);
    REQUIRE(gs.assertUpper(z, endpoint(10, 6)));
    REQUIRE(gs.assertLower(z, endpoint(4, 7)));
    REQUIRE(gs.assertUpper(z, endpoint(6, 8)));
    // This upper bound also leaves a derived pin's original proof valid.
    REQUIRE(gs.assertUpper(y, endpoint(4, 9)));
    CHECK(gs.sharedFixedValueAnalysis() == pinned);
    const auto fresh = gs.analyzeFixedValues();
    REQUIRE(fresh.prove(y));
    CHECK(fresh.prove(y)->first == pinned->prove(y)->first);
    CHECK_FALSE(fresh.prove(z));
    gs.push();
    REQUIRE(gs.assertLower(z, endpoint(6, 10), 1));
    CHECK(gs.sharedFixedValueAnalysis() != pinned);
    REQUIRE(gs.proveFixedValue(z));
    CHECK(gs.proveFixedValue(z)->first == DeltaRational(6));
    gs.pop(GeneralSimplex::AssignmentPolicy::Preserve);
    CHECK_FALSE(gs.proveFixedValue(z));
    CHECK(pinned->prove(y)->first == DeltaRational(3));
}

TEST_CASE("GeneralSimplex: replacing bound sources agrees with independent finite feasibility") {
    GeneralSimplex gs;
    const int x = gs.addVar("base-x"), y = gs.addVar("base-y");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    for (int step = 0; step < 120; ++step) {
        CAPTURE(step);
        std::vector<GeneralSimplex::ActiveBound> bounds;
        auto add = [&](int var, bool lower, int twice) {
            bounds.push_back({var, lower, BoundInfo(BoundValue(DeltaRational(mpq_class(twice, 2))),
                                                  SatLit::positive(bounds.size() + 1))});
        };
        add(x, true, -6); add(x, false, 6); add(y, true, -6); add(y, false, 6);
        add(x, true, (step * 5) % 13 - 6);
        add(x, false, (step * 7 + 2) % 13 - 6);
        add(sum, true, (step * 3) % 17 - 8);
        add(sum, false, (step * 11 + 3) % 17 - 8);
        auto satisfies = [&](const GeneralSimplex::ActiveBound& bound, int a, int b) {
            const mpq_class value(bound.var == x ? a : bound.var == y ? b : a + b, 2);
            return bound.isLower ? DeltaRational(value) >= bound.info.bound.value
                                 : DeltaRational(value) <= bound.info.bound.value;
        };
        bool exists = false;
        for (int a = -6; a <= 6; ++a) for (int b = -6; b <= 6; ++b) {
            bool valid = true;
            for (const auto& bound : bounds) valid &= satisfies(bound, a, b);
            exists |= valid;
        }
        gs.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve);
        const auto result = gs.check();
        CHECK(result == (exists ? GeneralSimplex::Result::Sat : GeneralSimplex::Result::Unsat));
        if (exists) {
            CHECK(gs.value(sum) == gs.value(x) + gs.value(y));
            for (const auto& bound : bounds)
                CHECK(bound.isLower ? gs.value(bound.var) >= bound.info.bound.value
                                    : gs.value(bound.var) <= bound.info.bound.value);
        } else {
            REQUIRE_FALSE(gs.getConflict().empty());
            // A conflict must already follow from just its returned premises.
            for (int a = -8; a <= 8; ++a) for (int b = -8; b <= 8; ++b) {
                bool premises = true;
                for (const auto& reason : gs.getConflict()) {
                    REQUIRE(reason.reason.var > 0);
                    REQUIRE(reason.reason.var <= bounds.size());
                    premises &= satisfies(bounds[reason.reason.var - 1], a, b);
                }
                CHECK_FALSE(premises);
            }
        }
        CHECK(gs.debugCheckInvariants());
    }
}

TEST_CASE("GeneralSimplex: a replaced base supports new scopes and sparse resets") {
    GeneralSimplex gs;
    const int x = gs.addVar("base-scope-x");
    for (int i = 0; i < 100; ++i) gs.addVar("unbounded-" + std::to_string(i));
    const auto lower = BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1));
    const auto upper = BoundInfo(BoundValue(DeltaRational(10)), SatLit::positive(2));
    REQUIRE(gs.replaceActiveBounds({{x, true, lower}, {x, false, upper}}));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    const auto snapshot = gs.sharedFixedValueAnalysis();
    CHECK_THROWS_AS(gs.replaceActiveBounds({{-1, true, lower}}), std::invalid_argument);
    CHECK(gs.sharedFixedValueAnalysis() == snapshot);
    gs.push();
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(5)), SatLit::positive(3)), 1));
    gs.pop(GeneralSimplex::AssignmentPolicy::Preserve);
    CHECK(gs.varState(x).lower.bound.value == DeltaRational(0));
    CHECK(gs.varState(x).upper.bound.value == DeltaRational(10));
    gs.resetActiveBounds();
    CHECK_FALSE(gs.varState(x).lower.bound.isFinite());
    CHECK_FALSE(gs.varState(x).upper.bound.isFinite());
    CHECK((gs.check() == GeneralSimplex::Result::Sat));
}

TEST_CASE("GeneralSimplex: replacement preserves incremental bound-event priority") {
    GeneralSimplex original;
    const int x = original.addVar("event-x"), y = original.addVar("event-y");
    const int sum = original.addConstraint({{x, 1}, {y, 1}}, 0);
    const int difference = original.addConstraint({{x, 1}, {y, -1}}, 0);
    REQUIRE((original.check() == GeneralSimplex::Result::Sat));
    GeneralSimplex incremental = original, bulk = original;
    auto lower = [](int value, int reason) {
        return BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason));
    };
    const std::vector<GeneralSimplex::ActiveBound> bounds{
        {sum, true, lower(-1, 1)}, {difference, true, lower(1, 2)}, {sum, true, lower(2, 3)}};
    incremental.resetActiveBounds(GeneralSimplex::AssignmentPolicy::Preserve);
    for (const auto& bound : bounds) REQUIRE(incremental.assertLower(bound.var, bound.info));
    REQUIRE(bulk.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve));
    REQUIRE((incremental.check() == GeneralSimplex::Result::Sat));
    REQUIRE((bulk.check() == GeneralSimplex::Result::Sat));
    for (int var = 0; var < original.numVars(); ++var) CHECK(bulk.value(var) == incremental.value(var));
    CHECK(bulk.value(sum) == bulk.value(x) + bulk.value(y));
    CHECK(bulk.value(difference) == bulk.value(x) - bulk.value(y));
}

TEST_CASE("GeneralSimplex: replacement reuses only unchanged fixed-value proof sources") {
    GeneralSimplex gs;
    const int x = gs.addVar("proof-source-x"), y = gs.addVar("proof-source-y");
    const int z = gs.addVar("proof-source-z");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 5);
    auto endpoint = [](int value, int reason) {
        return BoundInfo(BoundValue(DeltaRational(value)), SatLit::positive(reason));
    };
    std::vector<GeneralSimplex::ActiveBound> base{
        {x, true, endpoint(2, 1)}, {x, false, endpoint(2, 2)},
        {sum, true, endpoint(0, 3)}, {sum, false, endpoint(0, 4)},
        {z, true, endpoint(0, 5)}, {z, false, endpoint(10, 6)}};
    REQUIRE(gs.replaceActiveBounds(base));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    const auto pinned = gs.sharedFixedValueAnalysis();
    REQUIRE(pinned->prove(y));
    CHECK(pinned->prove(y)->first == DeltaRational(3));
    const auto revision = gs.boundRevision();
    base.back().info = endpoint(8, 7);
    REQUIRE(gs.replaceActiveBounds(base, GeneralSimplex::AssignmentPolicy::Preserve));
    CHECK(gs.boundRevision() != revision);
    CHECK(gs.sharedFixedValueAnalysis() == pinned);
    CHECK(pinned->prove(y)->first == gs.analyzeFixedValues().prove(y)->first);
    // Equal values with different reasons are different proof sources.
    base.front().info = endpoint(2, 8);
    REQUIRE(gs.replaceActiveBounds(base, GeneralSimplex::AssignmentPolicy::Preserve));
    const auto changed = gs.sharedFixedValueAnalysis();
    CHECK(changed != pinned);
    const auto proof = changed->prove(y);
    REQUIRE(proof);
    bool hasNewReason = false;
    for (const auto& premise : proof->second) {
        CHECK(premise.reason != SatLit::positive(1));
        hasNewReason |= premise.reason == SatLit::positive(8);
    }
    CHECK(hasNewReason);
    base.erase(base.begin() + 1); // remove x's upper pin
    REQUIRE(gs.replaceActiveBounds(base, GeneralSimplex::AssignmentPolicy::Preserve));
    CHECK_FALSE(gs.sharedFixedValueAnalysis()->prove(y));
    CHECK_FALSE(gs.analyzeFixedValues().prove(y));
    CHECK(pinned->prove(y)->first == DeltaRational(3));
}

TEST_CASE("GeneralSimplex: replacement normalizes rational endpoints transactionally") {
    GeneralSimplex gs;
    const int x = gs.addVar("rational-base-x");
    const auto endpoint = [](mpq_class a, mpq_class b, int reason) {
        return BoundInfo(BoundValue(DeltaRational(a, b)), SatLit::positive(reason));
    };
    const auto raw = endpoint(mpq_class(6, 4), mpq_class(4, 2), 1);
    REQUIRE(gs.replaceActiveBounds({{x, true, raw}, {x, false, raw}}));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(x) == DeltaRational(mpq_class(3, 2), 2));
    // Normalization belongs to the solver boundary; caller data is unchanged.
    CHECK(mpz_cmp_ui(mpq_denref(raw.bound.value.a.get_mpq_t()), 4) == 0);
    mpq_class negativeDenominator(3, 2);
    mpz_neg(mpq_denref(negativeDenominator.get_mpq_t()), mpq_denref(negativeDenominator.get_mpq_t()));
    const auto negative = endpoint(negativeDenominator, mpq_class(0, 2), 2);
    REQUIRE(gs.replaceActiveBounds({{x, true, negative}, {x, false, negative}},
                                  GeneralSimplex::AssignmentPolicy::Preserve));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(x) == DeltaRational(mpq_class(-3, 2)));
    const auto snapshot = gs.sharedFixedValueAnalysis();
    for (bool delta : {false, true}) {
        mpq_class zeroDenominator(1);
        mpz_set_ui(mpq_denref(zeroDenominator.get_mpq_t()), 0);
        const auto invalid = endpoint(delta ? mpq_class(0) : zeroDenominator,
                                      delta ? zeroDenominator : mpq_class(0), 3);
        CHECK_THROWS_AS(gs.replaceActiveBounds({{x, true, raw}, {x, false, invalid}}), std::invalid_argument);
        CHECK(gs.sharedFixedValueAnalysis() == snapshot);
        CHECK(gs.value(x) == DeltaRational(mpq_class(-3, 2)));
    }
}

TEST_CASE("GeneralSimplex: bound revisions invalidate rejected bounds, scopes and resets") {
    GeneralSimplex gs;
    const int x = gs.addVar("revision-x");
    auto previous = gs.boundRevision();
    REQUIRE(previous.has_value());
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
    CHECK(gs.boundRevision() != previous);
    previous = gs.boundRevision();
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(-1)), SatLit::positive(2))));
    CHECK(gs.boundRevision() == previous);
    gs.push();
    CHECK_FALSE(gs.assertUpper(x, BoundInfo(BoundValue(DeltaRational(-1)), SatLit::positive(3)), 1));
    CHECK(gs.boundRevision() != previous);
    previous = gs.boundRevision();
    gs.pop();
    CHECK(gs.boundRevision() != previous);
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    previous = gs.boundRevision();
    gs.backtrackToLevel(0);
    CHECK(gs.boundRevision() != previous);
    previous = gs.boundRevision();
    gs.resetActiveBounds();
    CHECK(gs.boundRevision() != previous);
    previous = gs.boundRevision();
    gs.reset();
    CHECK(gs.boundRevision() != previous);
}

TEST_CASE("GeneralSimplex: added rows preserve the current assignment and accept bound updates") {
    GeneralSimplex gs;
    const int x = gs.addVar("row-x"), y = gs.addVar("row-y");
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(2)), SatLit::positive(1))));
    REQUIRE(gs.assertLower(y, BoundInfo(BoundValue(DeltaRational(3)), SatLit::positive(2))));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    const auto oldX = gs.value(x), oldY = gs.value(y);
    const int difference = gs.addConstraint({{x, 2}, {y, -3}}, 1);
    CHECK(gs.value(x) == oldX);
    CHECK(gs.value(y) == oldY);
    CHECK(gs.value(difference) == mpq_class(2) * oldX - mpq_class(3) * oldY - DeltaRational(1));
    REQUIRE(gs.assertLower(difference, BoundInfo(BoundValue(DeltaRational(-5)), SatLit::positive(3))));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(difference) == mpq_class(2) * gs.value(x) - mpq_class(3) * gs.value(y) - DeltaRational(1));
    CHECK(gs.value(difference) >= DeltaRational(-5));
    const int z = gs.addVar("row-z");
    const int sum = gs.addConstraint({{difference, 1}, {z, 1}}, 0);
    CHECK(gs.value(sum) == gs.value(difference) + gs.value(z));
    REQUIRE(gs.assertLower(z, BoundInfo(BoundValue(DeltaRational(4)), SatLit::positive(4))));
    CHECK(gs.value(sum) == gs.value(difference) + gs.value(z));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    gs.resetActiveBounds();
    const int dirtyRow = gs.addConstraint({{x, 1}, {sum, -2}}, 7);
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(dirtyRow) == gs.value(x) - mpq_class(2) * gs.value(sum) - DeltaRational(7));
}

TEST_CASE("GeneralSimplex: bound reset explicitly selects assignment preservation or reinitialization") {
    GeneralSimplex gs;
    const int x = gs.addVar("warm-x"), y = gs.addVar("warm-y");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(7)), SatLit::positive(1))));
    REQUIRE(gs.assertLower(y, BoundInfo(BoundValue(DeltaRational(3)), SatLit::positive(2))));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    const auto beforeX = gs.value(x), beforeY = gs.value(y), beforeSum = gs.value(sum);
    gs.resetActiveBounds(GeneralSimplex::AssignmentPolicy::Preserve);
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(x) == beforeX);
    CHECK(gs.value(y) == beforeY);
    CHECK(gs.value(sum) == beforeSum);
    gs.resetActiveBounds();
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(x).isZero());
    CHECK(gs.value(y).isZero());
    CHECK(gs.value(sum).isZero());
}

TEST_CASE("GeneralSimplex: preserving a point from an infeasible context still repairs new bounds") {
    GeneralSimplex gs;
    const int x = gs.addVar("repair-x"), y = gs.addVar("repair-y");
    const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 0);
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
    REQUIRE(gs.assertLower(y, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(2))));
    REQUIRE(gs.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(3))));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(1)), SatLit::positive(4)), 1));
    REQUIRE((gs.check() == GeneralSimplex::Result::Unsat));
    gs.resetActiveBounds(GeneralSimplex::AssignmentPolicy::Preserve);
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
    REQUIRE(gs.assertLower(y, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(2))));
    REQUIRE(gs.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(3))));
    REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
    CHECK(gs.value(x).isZero());
    CHECK(gs.value(y).isZero());
    CHECK(gs.value(sum).isZero());
}

TEST_CASE("GeneralSimplex: explicit preserved rollback keeps feasible child points and repairs infeasible ones") {
    for (const bool infeasible : {false, true}) {
        GeneralSimplex gs;
        const int x = gs.addVar("policy-x"), y = gs.addVar("policy-y");
        const int sum = gs.addConstraint({{x, 1}, {y, 1}}, 0);
        REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(1))));
        REQUIRE(gs.assertLower(y, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(2))));
        if (infeasible)
            REQUIRE(gs.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(3))));
        REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
        gs.push();
        REQUIRE(gs.assertLower(x, BoundInfo(BoundValue(DeltaRational(7)), SatLit::positive(4)), 1));
        CHECK((gs.check() == (infeasible ? GeneralSimplex::Result::Unsat : GeneralSimplex::Result::Sat)));
        gs.pop(GeneralSimplex::AssignmentPolicy::Preserve);
        REQUIRE((gs.check() == GeneralSimplex::Result::Sat));
        CHECK(gs.value(x) == DeltaRational(infeasible ? 0 : 7));
        CHECK(gs.value(sum) == gs.value(x) + gs.value(y));
    }
}
