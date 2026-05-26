#include <doctest/doctest.h>
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <set>
#include <algorithm>

using namespace zolver;

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
