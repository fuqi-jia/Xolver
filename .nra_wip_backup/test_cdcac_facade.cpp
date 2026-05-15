#include <doctest/doctest.h>
#include "theory/arith/nra/CdcacSolver.h"
#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/ReasonManager.h"
#include "theory/arith/nra/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace nlcolver;

TEST_CASE("CDCAC facade: constant unsat conflict") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId eqPoly = kernel->sub(one, zero);  // 1 - 0 = 1

    SatLit reason = SatLit::positive(1);
    solver.assertConstraint(eqPoly, Relation::Eq, reason, 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
    REQUIRE(res.conflictOpt.has_value());
    CHECK(!res.conflictOpt->clause.empty());
    CHECK(res.conflictOpt->clause[0].var == reason.var);
    CHECK(res.conflictOpt->clause[0].sign == !reason.sign);
}

TEST_CASE("CDCAC facade: constant sat consistent") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId gtPoly = kernel->sub(one, zero);  // 1 - 0 = 1

    solver.assertConstraint(gtPoly, Relation::Gt, SatLit::positive(1), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC facade: effort cheap defers to full") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    // No constraints -> consistent regardless of effort
    auto cheap = solver.check(TheoryEffort::Cheap, nullptr);
    CHECK(cheap.kind == TheoryCheckResult::Kind::Consistent);

    auto standard = solver.check(TheoryEffort::Standard, nullptr);
    CHECK(standard.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC facade: backtrack clears pending conflict") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId eqPoly = kernel->sub(one, zero);

    SatLit reason = SatLit::positive(1);
    solver.assertConstraint(eqPoly, Relation::Eq, reason, 1);
    auto res1 = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res1.kind == TheoryCheckResult::Kind::Conflict);

    // Re-check should return cached conflict
    auto res2 = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res2.kind == TheoryCheckResult::Kind::Conflict);

    // Backtrack to level 0 clears the conflict
    solver.backtrack(0);
    auto res3 = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res3.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC facade: active constraint trail") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId p1 = kernel->mkConst(mpq_class(1));
    PolyId p2 = kernel->mkConst(mpq_class(2));
    PolyId p3 = kernel->mkConst(mpq_class(3));

    solver.assertConstraint(p1, Relation::Gt, SatLit::positive(1), 0);  // 1 > 0: true
    solver.assertConstraint(p2, Relation::Gt, SatLit::positive(2), 1);  // 2 > 0: true
    solver.assertConstraint(p3, Relation::Lt, SatLit::positive(3), 2);  // 3 < 0: false -> conflict

    // Backtrack to level 1 should keep first two constraints (both true)
    solver.backtrack(1);
    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC facade: reset clears everything") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId eqPoly = kernel->sub(one, zero);

    solver.assertConstraint(eqPoly, Relation::Eq, SatLit::positive(1), 0);
    solver.reset();

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC facade: univariate linear x=0 returns Consistent") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    // Create a polynomial with a variable: x (represented as variable "x")
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x = 0
    solver.assertConstraint(x, Relation::Eq, SatLit::positive(1), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("ReasonManager: deduplicate and toConflict") {
    std::vector<SatLit> reasons = {
        SatLit::positive(1),
        SatLit::positive(2),
        SatLit::positive(1),  // duplicate
    };
    auto deduped = ReasonManager::deduplicate(reasons);
    CHECK(deduped.size() == 2);

    auto conflict = ReasonManager::toConflict(deduped);
    REQUIRE(conflict.clause.size() == 2);
    CHECK(conflict.clause[0].var == 1);
    CHECK(conflict.clause[0].sign == false);
    CHECK(conflict.clause[1].var == 2);
    CHECK(conflict.clause[1].sign == false);
}

TEST_CASE("RealAlg: factory methods and accessors") {
    auto r = RealAlg::fromRational(mpq_class(42));
    CHECK(r.isRational());
    CHECK(r.rational == mpq_class(42));

    AlgebraicRoot ar;
    ar.rootIndex = 0;
    ar.lower = mpq_class(1);
    ar.upper = mpq_class(2);
    auto a = RealAlg::fromAlgebraic(ar);
    CHECK(a.isAlgebraic());
    CHECK(a.root.rootIndex == 0);
}

TEST_CASE("Bound: factory methods") {
    auto neg = Bound::negInf();
    CHECK(neg.isNegInf());

    auto pos = Bound::posInf();
    CHECK(pos.isPosInf());

    auto r = Bound::rational(mpq_class(5), true);
    CHECK(r.isRational());
    CHECK(r.open);
}

TEST_CASE("CDCAC: debug getIntegerCoefficients for x^2 - 2") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId x2m2 = kernel->sub(x2, two);

    CHECK(!kernel->isConstant(x2m2));
    auto vars = kernel->variables(x2m2);
    CHECK(vars.size() == 1);
    CHECK(vars[0] == "x");

    auto coeffs = kernel->getIntegerCoefficients(x2m2, "x");
    REQUIRE(coeffs.has_value());
    REQUIRE(coeffs->size() == 3);
    CHECK((*coeffs)[0] == mpz_class(1));   // x^2
    CHECK((*coeffs)[1] == mpz_class(0));   // x
    CHECK((*coeffs)[2] == mpz_class(-2));  // constant
}

TEST_CASE("CDCAC: univariate sat x^2 - 2 = 0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId x2m2 = kernel->sub(x2, two);

    // Verify that signAt works for a rational sample
    SamplePoint sp;
    sp.varOrder = {"x"};
    sp.values = {RealAlg::fromRational(mpq_class(2))};

    LibpolyBackend algebra(kernel.get());
    Sign s = algebra.signAt(x2m2, sp);
    CHECK(s == Sign::Pos);  // 2^2 - 2 = 2 > 0

    // Verify isolateRealRoots works
    UniPolyId up = algebra.specializeToUnivariate(x2m2, SamplePoint{}, "x");
    CHECK(up != NullUniPolyId);
    RootSet roots = algebra.isolateRealRoots(up);
    CHECK(roots.numRoots() == 2);
    CHECK(algebra.validateRootIsolation(up, roots));

    // Verify signAt at algebraic root returns Zero
    SamplePoint spAlg;
    spAlg.varOrder = {"x"};
    spAlg.values = {roots.roots[0]};
    Sign sAlg = algebra.signAt(x2m2, spAlg);
    CHECK(sAlg == Sign::Zero);

    solver.assertConstraint(x2m2, Relation::Eq, SatLit::positive(1), 0);
    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC: univariate unsat x^2 + 1 = 0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId x2 = kernel->pow(x, 2);
    PolyId x2p1 = kernel->add(x2, one);

    solver.assertConstraint(x2p1, Relation::Eq, SatLit::positive(1), 0);
    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

// ------------------------------------------------------------------
// P2a: univariate algebraic signAt + gcd zero detection tests
// ------------------------------------------------------------------

TEST_CASE("CDCAC: algebraic sat x^2=2") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId eq = kernel->sub(x2, two); // x^2 - 2 = 0

    solver.assertConstraint(eq, Relation::Eq, SatLit::positive(1), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC: algebraic unsat x^2=2 && x^2!=2") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId eq = kernel->sub(x2, two); // x^2 - 2 = 0

    solver.assertConstraint(eq, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(eq, Relation::Neq, SatLit::positive(2), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("CDCAC: algebraic unsat x^2=2 && (x^2-2)(x+1)!=0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId x2minus2 = kernel->sub(x2, two);       // x^2 - 2
    PolyId xplus1 = kernel->add(x, one);          // x + 1
    PolyId product = kernel->mul(x2minus2, xplus1); // (x^2 - 2)(x + 1)

    solver.assertConstraint(x2minus2, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(product, Relation::Neq, SatLit::positive(2), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("CDCAC: algebraic sat x^2=2 && x>0 && x-1>0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId eq = kernel->sub(x2, two);     // x^2 - 2 = 0
    PolyId gt0 = kernel->sub(x, zero);    // x > 0
    PolyId gt1 = kernel->sub(x, one);     // x - 1 > 0

    solver.assertConstraint(eq, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(gt0, Relation::Gt, SatLit::positive(2), 0);
    solver.assertConstraint(gt1, Relation::Gt, SatLit::positive(3), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC: algebraic unsat x^2=2 && x>0 && x-2>0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId x2 = kernel->pow(x, 2);
    PolyId eq = kernel->sub(x2, two);     // x^2 - 2 = 0
    PolyId gt0 = kernel->sub(x, zero);    // x > 0
    PolyId gt2 = kernel->sub(x, two);     // x - 2 > 0

    solver.assertConstraint(eq, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(gt0, Relation::Gt, SatLit::positive(2), 0);
    solver.assertConstraint(gt2, Relation::Gt, SatLit::positive(3), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("CDCAC: univariate unsat x^2 < 0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId x2 = kernel->pow(x, 2);

    // Debug: check roots of x^2
    LibpolyBackend algebra(kernel.get());
    UniPolyId up = algebra.specializeToUnivariate(x2, SamplePoint{}, "x");
    RootSet roots = algebra.isolateRealRoots(up);
    CHECK(roots.numRoots() >= 1);  // x^2 has a root at 0
    // Check each root (rational roots are canonicalized)
    for (int i = 0; i < roots.numRoots(); ++i) {
        if (roots.roots[i].isRational()) {
            CHECK(roots.roots[i].rational >= roots.roots[i].rational); // trivial
        } else {
            CHECK(roots.roots[i].isAlgebraic());
            CHECK(roots.roots[i].root.lower <= roots.roots[i].root.upper);
        }
    }

    // Debug: signAt at rational samples
    for (int q : {-1, 0, 1}) {
        SamplePoint sp;
        sp.varOrder = {"x"};
        sp.values = {RealAlg::fromRational(mpq_class(q))};
        Sign s = algebra.signAt(x2, sp);
        CHECK(s != Sign::Unknown);
    }

    // Debug: sgn directly
    std::unordered_map<std::string, mpq_class> m1{{"x", mpq_class(-1)}};
    std::unordered_map<std::string, mpq_class> m0{{"x", mpq_class(0)}};
    int s_neg1 = kernel->sgn(x2, m1);
    int s_0 = kernel->sgn(x2, m0);
    CHECK(s_neg1 == 1);   // x^2 at -1 = 1 > 0
    CHECK(s_0 == 0);      // x^2 at 0 = 0

    // Debug: variables of x^2
    auto vars = kernel->variables(x2);
    CHECK(vars.size() == 1);
    CHECK(vars[0] == "x");

    solver.assertConstraint(x2, Relation::Lt, SatLit::positive(1), 0);
    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

// ------------------------------------------------------------------
// P2a: multivariate recursive framework + rational sample
// ------------------------------------------------------------------

TEST_CASE("CDCAC: multivariate sat x*y=1, x=1, y=1") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId xy = kernel->mul(x, y);
    PolyId eq1 = kernel->sub(xy, one); // x*y - 1 = 0
    PolyId eq2 = kernel->sub(x, one);  // x - 1 = 0
    PolyId eq3 = kernel->sub(y, one);  // y - 1 = 0

    solver.assertConstraint(eq1, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(eq2, Relation::Eq, SatLit::positive(2), 0);
    solver.assertConstraint(eq3, Relation::Eq, SatLit::positive(3), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("CDCAC: multivariate unsat x*y=0, x!=0, y!=0") {
    auto kernel = createPolynomialKernel();
    CdcacSolver solver(kernel.get());

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId zero = kernel->mkConst(mpq_class(0));
    PolyId xy = kernel->mul(x, y);
    PolyId eq1 = kernel->sub(xy, zero); // x*y = 0
    PolyId neq1 = kernel->sub(x, zero); // x != 0
    PolyId neq2 = kernel->sub(y, zero); // y != 0

    solver.assertConstraint(eq1, Relation::Eq, SatLit::positive(1), 0);
    solver.assertConstraint(neq1, Relation::Neq, SatLit::positive(2), 0);
    solver.assertConstraint(neq2, Relation::Neq, SatLit::positive(3), 0);

    auto res = solver.check(TheoryEffort::Full, nullptr);
    CHECK(res.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("P4: isolateRealRootsAlgebraic with sqrt(2) prefix") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    // y^2 - 2 = 0  ->  y = ±sqrt(2)
    VarId yVar = kernel->getOrCreateVar("y");
    PolyId y = kernel->mkVar(yVar);
    PolyId y2 = kernel->pow(y, 2);
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId y2m2 = kernel->sub(y2, two);

    UniPolyId upY = algebra.specializeToUnivariate(y2m2, SamplePoint{}, "y");
    REQUIRE(upY != NullUniPolyId);
    RootSet yRoots = algebra.isolateRealRoots(upY);
    CHECK(yRoots.numRoots() == 2);

    // Find the positive root (sqrt(2))
    CompareResult cmp0 = algebra.compareRealAlg(yRoots.roots[0], RealAlg::fromRational(mpq_class(0)));
    const RealAlg& sqrt2 = (cmp0 == CompareResult::Greater) ? yRoots.roots[0] : yRoots.roots[1];
    REQUIRE(sqrt2.isAlgebraic());

    // x^2 + y^2 - 3  with  y = sqrt(2)  ->  x^2 - 1 = 0  ->  x = ±1
    VarId xVar = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(xVar);
    PolyId x2 = kernel->pow(x, 2);
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId x2p_y2m3 = kernel->add(x2, kernel->sub(y2, three));

    SamplePoint prefix;
    prefix.push("y", sqrt2);

    RootSet xRoots = algebra.isolateRealRootsAlgebraic(x2p_y2m3, prefix, "x");
    CHECK(xRoots.numRoots() == 2);

    // Verify the two roots straddle 0 (one negative, one positive).
    bool hasNegative = false;
    bool hasPositive = false;
    for (const auto& r : xRoots.roots) {
        if (r.isRational()) {
            if (r.rational < 0) hasNegative = true;
            if (r.rational > 0) hasPositive = true;
        } else if (r.isAlgebraic()) {
            if (r.root.upper < 0) hasNegative = true;
            if (r.root.lower > 0) hasPositive = true;
        }
    }
    CHECK(hasNegative);
    CHECK(hasPositive);
}
