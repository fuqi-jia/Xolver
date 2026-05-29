// CAC single-cell projection (module B — characterize). Verifies the Lazard
// projection is split correctly into this-level boundary polys (contain elimVar)
// vs the downward characterization (free of elimVar), matching known cells.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/cac/SingleCellProjection.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"
#endif

using namespace xolver;

static RealValue Q(long n, long d = 1) { return RealValue::fromMpq(mpq_class(n, d)); }

static const VarId VX = VarId{1}, VY = VarId{2};

static RationalPolynomial konst(long c) { return RationalPolynomial::fromConstant(mpq_class(c)); }

// y^2 - x
static RationalPolynomial yy_minus_x() {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize(); return p;
}
// x^2 + y^2 - 1
static RationalPolynomial circle() {
    RationalPolynomial p; p.addVar(VX, 2, 1); p.addVar(VY, 2, 1);
    p = p + konst(-1); p.normalize(); return p;
}

static bool hasPolyInXOnly(const std::vector<RationalPolynomial>& v) {
    for (const auto& p : v) if (p.degree(VY) == 0 && p.degree(VX) >= 1) return true;
    return false;
}

TEST_CASE("characterize: y^2 - x eliminate y") {
    auto r = characterize({yy_minus_x()}, VY);
    CHECK(r.complete);
    // The squarefree factor y^2 - x stays in y as this level's boundary.
    REQUIRE(r.boundaryPolys.size() >= 1);
    for (const auto& p : r.boundaryPolys) CHECK(p.degree(VY) >= 1);
    // The discriminant / trailing coeff (~ x) is the downward boundary.
    CHECK(hasPolyInXOnly(r.downwardPolys));
    for (const auto& p : r.downwardPolys) CHECK(p.degree(VY) == 0);
}

TEST_CASE("characterize: circle x^2 + y^2 - 1 eliminate y") {
    auto r = characterize({circle()}, VY);
    CHECK(r.complete);
    REQUIRE(r.boundaryPolys.size() >= 1);
    // Discriminant in y is ~ (1 - x^2): a downward poly in x only.
    CHECK(hasPolyInXOnly(r.downwardPolys));
}

TEST_CASE("characterize: resultant of two lines in y") {
    // y - x and y - 2 : res_y = (x - 2), a downward poly in x only.
    RationalPolynomial a; a.addVar(VY, 1, 1); a.addVar(VX, 1, -1); a.normalize();   // y - x
    RationalPolynomial b; b.addVar(VY, 1, 1); b = b + konst(-2); b.normalize();     // y - 2
    auto r = characterize({a, b}, VY);
    CHECK(r.complete);
    CHECK(hasPolyInXOnly(r.downwardPolys));
}

TEST_CASE("characterize: empty input is complete and empty") {
    auto r = characterize({}, VY);
    CHECK(r.complete);
    CHECK(r.boundaryPolys.empty());
    CHECK(r.downwardPolys.empty());
}

TEST_CASE("characterize: no constants leak into either bucket") {
    auto r = characterize({circle()}, VY);
    for (const auto& p : r.boundaryPolys) CHECK_FALSE(p.isConstant());
    for (const auto& p : r.downwardPolys) CHECK_FALSE(p.isConstant());
}

#ifdef XOLVER_HAS_LIBPOLY
// x^2 - 2 in variable `x` (registered with the kernel).
static RationalPolynomial xsq_minus_2(VarId x) {
    RationalPolynomial p; p.addVar(x, 2, 1); p = p + konst(-2); p.normalize(); return p;
}

TEST_CASE("intervalFromCharacterization: x^2-2, sample 0 -> (-√2, √2)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    SamplePoint prefix;   // x is level 0: empty prefix
    auto r = intervalFromCharacterization(&backend, kernel.get(), {xsq_minus_2(x)},
                                          prefix, x, RealAlg::fromRational(mpq_class(0)));
    REQUIRE(r.supported);
    CHECK(r.interval.contains(Q(0)));
    CHECK(r.interval.contains(Q(1)));
    CHECK_FALSE(r.interval.contains(Q(2)));
    CHECK_FALSE(r.interval.contains(Q(-2)));
    // endpoints ≈ ±√2 (1.41 < √2 < 1.42): validates the algebraic conversion.
    CHECK(r.interval.contains(Q(141, 100)));
    CHECK_FALSE(r.interval.contains(Q(142, 100)));
    CHECK(r.interval.contains(Q(-141, 100)));
    CHECK_FALSE(r.interval.contains(Q(-142, 100)));
}

TEST_CASE("intervalFromCharacterization: x^2-2, sample 2 -> (√2, +inf)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    SamplePoint prefix;
    auto r = intervalFromCharacterization(&backend, kernel.get(), {xsq_minus_2(x)},
                                          prefix, x, RealAlg::fromRational(mpq_class(2)));
    REQUIRE(r.supported);
    CHECK(r.interval.contains(Q(2)));
    CHECK(r.interval.contains(Q(100)));
    CHECK(r.interval.contains(Q(142, 100)));    // just above √2
    CHECK_FALSE(r.interval.contains(Q(141, 100)));  // just below √2
    CHECK_FALSE(r.interval.contains(Q(0)));
}

TEST_CASE("intervalFromCharacterization: non-leaf rational nullification -> Lazard residual root") {
    // q = (x-1)*y nullifies at the rational prefix x=1 (q ≡ 0 in y). A non-leaf
    // (projection-factor) nullification must NOT be skipped: its Lazard valuation
    // residual is y (divide (x-1)*y by (x-1) -> y, substitute x=1 -> y), whose
    // root y=0 is a genuine lifting boundary. Skipping it would give the whole
    // y-axis (cell too large -> false UNSAT). With sample y=1 the cell is (0,+inf).
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial xm1; xm1.addVar(x, 1, 1); xm1 = xm1 + konst(-1); xm1.normalize();  // x-1
    RationalPolynomial yy;  yy.addVar(y, 1, 1); yy.normalize();                            // y
    RationalPolynomial q = xm1 * yy; q.normalize();                                        // (x-1)*y
    SamplePoint prefix; prefix.push(x, RealAlg::fromRational(mpq_class(1)));               // x=1
    auto r = intervalFromCharacterization(&backend, kernel.get(), {q},
                                          prefix, y, RealAlg::fromRational(mpq_class(1)),
                                          /*skipVanishing=*/false);
    REQUIRE(r.supported);                       // residual recovered (NOT bailed, NOT skipped)
    CHECK(r.interval.contains(Q(1)));           // sample side
    CHECK(r.interval.contains(Q(1000)));
    CHECK_FALSE(r.interval.contains(Q(0)));     // boundary at residual root y=0
    CHECK_FALSE(r.interval.contains(Q(-1)));    // other side excluded ⇒ cell is NOT the whole axis
}

TEST_CASE("intervalFromCharacterization: leaf rational nullification -> skip (whole axis)") {
    // SAME nullifying q, but as a LEAF constraint (skipVanishing=true): a constraint
    // ≡0 on the fiber has uniform truth (decided by signAt), so it adds no boundary
    // and the cell is the whole axis. This is the leaf/non-leaf asymmetry.
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial xm1; xm1.addVar(x, 1, 1); xm1 = xm1 + konst(-1); xm1.normalize();
    RationalPolynomial yy;  yy.addVar(y, 1, 1); yy.normalize();
    RationalPolynomial q = xm1 * yy; q.normalize();
    SamplePoint prefix; prefix.push(x, RealAlg::fromRational(mpq_class(1)));
    auto r = intervalFromCharacterization(&backend, kernel.get(), {q},
                                          prefix, y, RealAlg::fromRational(mpq_class(1)),
                                          /*skipVanishing=*/true);
    REQUIRE(r.supported);
    CHECK(r.interval.contains(Q(1)));
    CHECK(r.interval.contains(Q(0)));           // no boundary ⇒ whole axis
    CHECK(r.interval.contains(Q(-1000)));
}

TEST_CASE("intervalFromCharacterization: square-free reduction preserves ALL roots (no too-big cell)") {
    // ★ Soundness, the UNSOUND direction: the witness square-free reduction must
    // never DROP a genuine root boundary (that would enlarge the cell ⇒ claim
    // sign-invariance across a real root ⇒ false-UNSAT / wrong sample). Two
    // boundary polys stress exactly what the reduction touches:
    //   p1 = (y-1)^2 (y-2)  — a REPEATED factor (y-1) the square-free step collapses
    //   p2 = (y-1)(y+3)     — a SHARED factor (y-1) the cross-poly dedup removes
    // Genuine roots are {-3, 1, 2}. Sample y=-2 sits in (-3, 1); the cell must be
    // bounded by BOTH neighboring roots — proving neither the collapsed multiplicity
    // (root 1) nor the deduped/other factor (root -3) was lost.
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId y = kernel->getOrCreateVar("y");
    auto lin = [&](long r) { RationalPolynomial p; p.addVar(y, 1, 1); p = p + konst(-r); p.normalize(); return p; };
    RationalPolynomial p1 = lin(1) * lin(1) * lin(2);   // (y-1)^2 (y-2)
    RationalPolynomial p2 = lin(1) * lin(-3);           // (y-1)(y+3)
    p1.normalize(); p2.normalize();
    SamplePoint prefix;   // y is level 0: empty prefix
    auto r = intervalFromCharacterization(&backend, kernel.get(), {p1, p2},
                                          prefix, y, RealAlg::fromRational(mpq_class(-2)));
    REQUIRE(r.supported);
    CHECK(r.interval.contains(Q(-2)));        // sample inside
    CHECK(r.interval.contains(Q(0)));         // interior of (-3, 1)
    CHECK_FALSE(r.interval.contains(Q(-4)));  // PAST root -3 ⇒ -3 NOT dropped (cross-poly dedup safe)
    CHECK_FALSE(r.interval.contains(Q(1)));   // bounded by root 1 (collapsed (y-1)^2 still a boundary)
    CHECK_FALSE(r.interval.contains(Q(2)));   // root 2 is beyond the (-3,1) cell
}

TEST_CASE("intervalFromCharacterization: positive-definite x^2+1 -> whole axis") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial p; p.addVar(x, 2, 1); p = p + konst(1); p.normalize();  // x^2 + 1
    SamplePoint prefix;
    auto r = intervalFromCharacterization(&backend, kernel.get(), {p},
                                          prefix, x, RealAlg::fromRational(mpq_class(0)));
    REQUIRE(r.supported);          // no real roots ⇒ sign-invariant on all of ℝ
    CHECK(r.interval.contains(Q(0)));
    CHECK(r.interval.contains(Q(1000)));
    CHECK(r.interval.contains(Q(-1000)));
}
#endif  // XOLVER_HAS_LIBPOLY
