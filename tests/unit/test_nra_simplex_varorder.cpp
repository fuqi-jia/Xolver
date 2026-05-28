#include <doctest/doctest.h>
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <set>
#include <algorithm>

using namespace xolver;

static CdcacConstraint mkC(PolyId p, Relation r, int litVar) {
    CdcacConstraint c;
    c.poly = p; c.rel = r; c.reason = SatLit::positive(litVar);
    return c;
}

TEST_CASE("extractor: 2x + 3 >= 0 is linear with coeff 2 const 3") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId p = kernel->add(kernel->mul(two, x), three);  // 2x + 3

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Geq, 1) });
    REQUIRE(cc.linear.size() == 1);
    CHECK(cc.nonlinear.empty());
    const auto& la = cc.linear[0];
    REQUIRE(la.coeffs.size() == 1);
    CHECK(la.coeffs[0].first == kernel->getOrCreateVar("x"));
    CHECK(la.coeffs[0].second == mpq_class(2));
    CHECK(la.constant == mpq_class(3));
    CHECK(la.rel == Relation::Geq);
}

TEST_CASE("extractor: x*y - 1 is nonlinear") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId p = kernel->sub(kernel->mul(x, y), one);  // x*y - 1

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Eq, 1) });
    CHECK(cc.linear.empty());
    CHECK(cc.nonlinear.size() == 1);
}

#include "theory/arith/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/lra/SparseTableau.h"

TEST_CASE("deriveBasicInterval: x = 1 - y over y in [0,1] -> [0,1]") {
    // xb = rhs + sum coeff*col ; here rhs=1, one term coeff=-1 with col bounds [0,1]
    std::vector<RowTermBound> terms = { RowTermBound{ mpq_class(-1), mpq_class(0), mpq_class(1) } };
    auto iv = deriveBasicInterval(mpq_class(1), terms);
    REQUIRE(iv.first.has_value());  CHECK(*iv.first  == mpq_class(0));
    REQUIRE(iv.second.has_value()); CHECK(*iv.second == mpq_class(1));
}

TEST_CASE("deriveBasicInterval: missing lower bound on a positive-coeff term drops lower side") {
    std::vector<RowTermBound> terms = { RowTermBound{ mpq_class(2), std::nullopt, mpq_class(5) } };
    auto iv = deriveBasicInterval(mpq_class(0), terms);
    CHECK(!iv.first.has_value());                   // lower needs col-lower (positive coeff) -> missing
    REQUIRE(iv.second.has_value()); CHECK(*iv.second == mpq_class(10));
}

TEST_CASE("tableau facts: x>=1 and x<=1 (single-var) -> fixed; bounded both sides") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(xv);
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId xm1 = kernel->sub(x, one);
    auto cc = classifyConstraints(*kernel, {
        mkC(xm1, Relation::Geq, 1), mkC(xm1, Relation::Leq, 2) });
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    CHECK(!f.linearSubsetUnsat());
    CHECK(f.hasLower(xv)); CHECK(f.hasUpper(xv)); CHECK(f.isFixed(xv));
}

TEST_CASE("tableau facts: x>=1 and x<=0 (single-var) -> linearSubsetUnsat, no facts, no conflict") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(xv);
    PolyId one = kernel->mkConst(mpq_class(1));
    auto cc = classifyConstraints(*kernel, {
        mkC(kernel->sub(x, one), Relation::Geq, 1),   // x >= 1
        mkC(x,                   Relation::Leq, 2) }); // x <= 0
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    CHECK(f.linearSubsetUnsat());
    CHECK(!f.hasLower(xv));  // no ordering facts on UNSAT
}

TEST_CASE("tableau row convention: value(basic) == rhs + sum coeff*value(col)") {
    // Build x + y = 1, 0<=y<=1, x<=5 ; solve; verify the affine row identity
    // that deriveBasicInterval relies on. Pins the sign convention empirically.
    GeneralSimplex gs;
    int xi = gs.addVar("x"), yi = gs.addVar("y");
    int s = gs.addConstraint({ {xi, mpq_class(1)}, {yi, mpq_class(1)} }, mpq_class(0)); // s = x+y
    gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(1)));
    gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(1))); // x+y = 1
    gs.assertLower(yi, BoundInfo(BoundValue(DeltaRational(mpq_class(0))), SatLit::positive(2)));
    gs.assertUpper(yi, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(3)));
    gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(mpq_class(5))), SatLit::positive(4)));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    for (int r = 0; r < gs.tableau().numRows(); ++r) {
        const SparseRow& row = gs.tableau().row(r);
        if (row.basicVar < 0) continue;
        DeltaRational lhs = gs.value(row.basicVar);
        mpq_class accA = row.rhs, accB = 0;
        for (const auto& e : row.entries) {
            DeltaRational cv = gs.value(e.col);
            accA += e.coeff * cv.a;
            accB += e.coeff * cv.b;
        }
        CHECK(lhs.a == accA);
        CHECK(lhs.b == accB);
    }
}

TEST_CASE("tableau facts: an ORIGINAL variable acquires a row-derived bound (end-to-end)") {
    // x + y = 5 ; y fixed at 2 ; x has NO direct single-variable bound.
    // y sits at its (only) bound and cannot move, so the simplex MUST pivot x into
    // the basis to satisfy s = x+y = 5. x's row then derives x purely from the
    // non-basic bounds (s, y) -> proves row-derived bounds reach the facts for an
    // original variable (not just the aux var). This is the headline behavior;
    // without it the module degrades to "stored bounds + participation".
    // (Integer constants only: libpoly's integer-ring polynomials cannot represent
    // a non-integer rational like 1/4 — mkConst(1/4) returns NullPoly and crashes.)
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv);
    PolyId five = kernel->mkConst(mpq_class(5)), two = kernel->mkConst(mpq_class(2));
    auto cc = classifyConstraints(*kernel, {
        mkC(kernel->sub(kernel->add(x, y), five), Relation::Eq, 1),   // x + y - 5 = 0  (multi-var -> aux row)
        mkC(kernel->sub(y, two),                  Relation::Eq, 2) }); // y - 2 = 0      (single-var -> y fixed)
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    REQUIRE(!f.linearSubsetUnsat());
    REQUIRE(f.isBasic(xv));            // construction forces x basic; if this fails, adjust the construction
    // x has NO direct bound atom, so these bounds can ONLY be row-derived:
    CHECK(f.hasLower(xv));
    CHECK(f.hasUpper(xv));
    CHECK(f.isFixed(xv));             // x = 5 - 2 = 3
}

#include "theory/arith/nra/simplex/PolyStructureFacts.h"

TEST_CASE("structure: xy+xz-3 -> fixing x linearizes; fixing y/z does not") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y"), zv = kernel->getOrCreateVar("z");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv), z = kernel->mkVar(zv);
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId p = kernel->sub(kernel->add(kernel->mul(x, y), kernel->mul(x, z)), three); // xy+xz-3
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(xv) == 1);
    CHECK(f.linearizationGain(yv) == 0);
    CHECK(f.linearizationGain(zv) == 0);
    CHECK(f.nonlinearConnectivity(xv) == 2);
    CHECK(f.nonlinearConnectivity(yv) == 1);
}

TEST_CASE("structure: xyz -> fixing any one variable does NOT linearize (residual degree 2)") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y"), zv = kernel->getOrCreateVar("z");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv), z = kernel->mkVar(zv);
    PolyId p = kernel->mul(kernel->mul(x, y), z);   // x*y*z
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(xv) == 0);
    CHECK(f.linearizationGain(yv) == 0);
    CHECK(f.linearizationGain(zv) == 0);
}

TEST_CASE("structure: x*y^2 -> fixing y linearizes, fixing x does not") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv);
    PolyId p = kernel->mul(x, kernel->pow(y, 2));   // x*y^2
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(yv) == 1);
    CHECK(f.linearizationGain(xv) == 0);
    CHECK(f.maxDegree(yv) == 2);
}

#include "theory/arith/nra/simplex/VarOrderSelector.h"

static int posOf(const std::vector<std::string>& v, const std::string& n) {
    return (int)(std::find(v.begin(), v.end(), n) - v.begin());
}

TEST_CASE("varorder: highest total degree goes last (projected first)") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));
    PolyId three = kernel->mkConst(mpq_class(3)), two = kernel->mkConst(mpq_class(2));
    PolyId core = kernel->sub(kernel->add(kernel->mul(x, y), kernel->mul(x, z)), three);
    PolyId ym2 = kernel->sub(y, two), zm2 = kernel->sub(z, two);
    // Integer constant only: libpoly's integer-ring polynomials cannot represent a
    // non-integer rational (mkConst(1/2) returns NullPoly -> sub() derefs null -> SIGSEGV).
    // x-1 still makes degree(x) contribute, so x ties on total-degree with y,z, then
    // wins the frontScore tie-break (x linearizes xy+xz) to land LAST.
    PolyId xm1 = kernel->sub(x, kernel->mkConst(mpq_class(1)));
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = {
        C(core, Relation::Eq, 1), C(ym2, Relation::Geq, 2),
        C(zm2, Relation::Geq, 3), C(xm1, Relation::Leq, 4) };
    std::vector<std::string> names = {"x", "y", "z"};
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    REQUIRE(order.size() == 3);
    CHECK(order.back() == "x");                               // x has the highest degSum
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"x", "y", "z"});
}

TEST_CASE("varorder: within equal degree, higher linearization-gain var is later") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId a = kernel->mkVar(kernel->getOrCreateVar("a"));
    PolyId b = kernel->mkVar(kernel->getOrCreateVar("b"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId c1 = kernel->sub(kernel->mul(a, x), one);                       // a*x - 1  (fixing a linearizes)
    PolyId c2 = kernel->sub(kernel->mul(kernel->mul(b, x), y), one);       // b*x*y - 1 (fixing b leaves x*y)
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = { C(c1, Relation::Eq, 1), C(c2, Relation::Eq, 2) };
    std::vector<std::string> names = {"a", "b", "x", "y"};                  // a,b,y degSum 1; x degSum 2
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    CHECK(order.back() == "x");                                            // highest degree last
    CHECK(posOf(order, "a") > posOf(order, "b"));                          // a linearizes -> later than b
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"a","b","x","y"});
}

TEST_CASE("varorder: all-linear input is a valid deterministic permutation") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = { C(x, Relation::Geq, 1), C(y, Relation::Leq, 2) };
    std::vector<std::string> names = {"x", "y"};
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"x", "y"});
}

#include "theory/arith/nra/core/CdcacSolver.h"
#include <cstdlib>

TEST_CASE("cdcac varorder flag: same verdict on/off for xy + x^2 - 2 = 0 and y>=1") {
    auto run = [](bool on) {
        if (on) setenv("XOLVER_NRA_VARORDER_SIMPLEX", "1", 1);
        else    unsetenv("XOLVER_NRA_VARORDER_SIMPLEX");
        auto kernel = createPolynomialKernel();
        CdcacSolver solver(kernel.get());
        PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
        PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
        PolyId one = kernel->mkConst(mpq_class(1)), two = kernel->mkConst(mpq_class(2));
        PolyId core = kernel->sub(kernel->add(kernel->mul(x, y), kernel->pow(x, 2)), two);
        PolyId ym1 = kernel->sub(y, one);
        solver.assertConstraint(core, Relation::Eq,  SatLit::positive(1), 0);
        solver.assertConstraint(ym1,  Relation::Geq, SatLit::positive(2), 0);
        auto r = solver.check(CdcacEffort::Full, nullptr);
        return r.kind;
    };
    auto off = run(false);
    auto on  = run(true);
    unsetenv("XOLVER_NRA_VARORDER_SIMPLEX");
    CHECK(off == on);   // order must not change the verdict on a decidable case
}
