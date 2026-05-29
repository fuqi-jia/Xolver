// compareRealAlg certified-comparator contract (CAC.md "certified comparator").
// Equality certificate (identity / minpoly / gcd-membership) + separation
// certificate (refine to disjoint). Never guess: no math order without a proof.
// These pin the spec and reveal where the current comparator is incomplete.

#include <doctest/doctest.h>
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace xolver;

namespace {
RealAlg algRoot(UniPolyId p, int idx, const mpq_class& lo, const mpq_class& hi) {
    AlgebraicRoot a; a.definingPoly = p; a.rootIndex = idx; a.lower = lo; a.upper = hi;
    return RealAlg::fromAlgebraic(std::move(a));
}
}

// T1: same defining poly + same rootIndex ⇒ Equal (identity).
TEST_CASE("compareRealAlg T1: same poly same rootIndex -> Equal") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId xx2 = algebra.allocUni({1, 0, -2});            // x^2 - 2
    RealAlg a = algRoot(xx2, 1, mpq_class(1), mpq_class(2));  // sqrt(2)
    RealAlg b = algRoot(xx2, 1, mpq_class(1), mpq_class(2));
    CHECK(algebra.compareRealAlg(a, b) == CompareResult::Equal);
}

// T2: same defining poly + different rootIndex ⇒ order by index, NO refine.
TEST_CASE("compareRealAlg T2: same poly different rootIndex -> ordered") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId xx2 = algebra.allocUni({1, 0, -2});                  // x^2 - 2
    RealAlg neg = algRoot(xx2, 0, mpq_class(-2), mpq_class(-1));    // -sqrt(2)
    RealAlg pos = algRoot(xx2, 1, mpq_class(1), mpq_class(2));      //  sqrt(2)
    CHECK(algebra.compareRealAlg(neg, pos) == CompareResult::Less);
    CHECK(algebra.compareRealAlg(pos, neg) == CompareResult::Greater);
}

// T3: different defining polys, SAME value ⇒ Equal via gcd-membership.
// sqrt(2) as a root of x^2-2 vs as a root of (x^2-2)(x^2-3) = x^4-5x^2+6.
TEST_CASE("compareRealAlg T3: different poly same value -> Equal via gcd") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId xx2  = algebra.allocUni({1, 0, -2});            // x^2 - 2,  sqrt2 idx1
    UniPolyId quar = algebra.allocUni({1, 0, -5, 0, 6});      // x^4-5x^2+6, roots -√3,-√2,√2,√3
    RealAlg a = algRoot(xx2,  1, mpq_class(1), mpq_class(2));         // sqrt(2)
    RealAlg b = algRoot(quar, 2, mpq_class(1), mpq_class(mpq_class(3,2)));  // sqrt(2) (idx2 in quartic)
    CompareResult c = algebra.compareRealAlg(a, b);
    CHECK(c != CompareResult::Less);
    CHECK(c != CompareResult::Greater);   // must be Equal (or Unknown if incomplete) — NEVER a strict order
    CHECK(c == CompareResult::Equal);      // the spec target
}

// T4: coprime polys, DISTINCT roots ⇒ certified order, NEVER Equal.
// sqrt(2) (x^2-2) vs sqrt(3) (x^2-3); gcd = 1.
TEST_CASE("compareRealAlg T4: coprime distinct roots -> ordered, never Equal") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId xx2 = algebra.allocUni({1, 0, -2});            // sqrt2
    UniPolyId xx3 = algebra.allocUni({1, 0, -3});            // sqrt3
    RealAlg s2 = algRoot(xx2, 1, mpq_class(1), mpq_class(2));
    RealAlg s3 = algRoot(xx3, 1, mpq_class(1), mpq_class(2));   // deliberately wide/overlapping intervals
    CompareResult c = algebra.compareRealAlg(s2, s3);
    CHECK(c != CompareResult::Equal);              // distinct ⇒ never Equal (soundness)
    CHECK(c == CompareResult::Less);               // sqrt2 < sqrt3 (completeness target)
}

// R1: standalone reproducer of a real meti-tarski sort-compare-unknown failure
// (Pair B from /tmp/cac_repro_compare.txt, sin-problem-7-weak family). Two roots
// in [0,1/4] from different high-degree polys; the comparator currently returns
// Unknown. This test pins the reproducer + reveals equal-vs-distinct via gcd, to
// drive the [P0] algebraic-kernel completion.
TEST_CASE("compareRealAlg R1: high-degree meti-tarski pair (sort-compare-unknown repro)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    // a: 1000x^7 - 42000x^5 + 840000x^3 - 798000x + 2121, root idx1 in [0,1/4]
    UniPolyId pa = algebra.allocUni({1000, 0, -42000, 0, 840000, 0, -798000, 2121});
    // b: 40000x^3 - 38000x + 101, root idx1 in [0,1/4]
    UniPolyId pb = algebra.allocUni({40000, 0, -38000, 101});
    RealAlg a = algRoot(pa, 1, mpq_class(0), mpq_class(1, 4));
    RealAlg b = algRoot(pb, 1, mpq_class(0), mpq_class(1, 4));

    // Diagnose equal-vs-distinct via gcd (drives the fix; not an assertion yet).
    UniPolyId g = algebra.gcdUni(pa, pb);
    const bool coprime = (g == NullUniPolyId) || algebra.isConstantUni(g);
    MESSAGE("R1 gcd coprime=" << coprime);

    CompareResult c = algebra.compareRealAlg(a, b);
    MESSAGE("R1 compareRealAlg = " << static_cast<int>(c));
    // SOUNDNESS: distinct (coprime) ⇒ never Equal.
    if (coprime) CHECK(c != CompareResult::Equal);
    // COMPLETENESS ([P0], after the refineRootInterval local-bisection fix): the
    // two roots are ~1e-8 apart, so certified separation MUST decide the order
    // (Less or Greater — direction by disjoint intervals, not asserted here).
    CHECK(c != CompareResult::Unknown);
    CHECK((c == CompareResult::Less || c == CompareResult::Greater));
}

// R2: sin-problem-7-weak2 pair — roots ~2^-65 apart (a = 1000x^7-42000x^5+21*b),
// so the 64-cap couldn't separate them; proven-distinct (coprime) refine must.
TEST_CASE("compareRealAlg R2: ~2^-65-apart distinct roots (proven-distinct refine)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId pa = algebra.allocUni({1000, 0, -42000, 0, 840000, 0, -4158000, 1323});
    UniPolyId pb = algebra.allocUni({40000, 0, -198000, 63});
    RealAlg a = algRoot(pa, 1, mpq_class(0), mpq_class(1, 4));
    RealAlg b = algRoot(pb, 1, mpq_class(0), mpq_class(1, 4));
    CompareResult c = algebra.compareRealAlg(a, b);
    CHECK(c != CompareResult::Equal);
    CHECK(c != CompareResult::Unknown);
    CHECK((c == CompareResult::Less || c == CompareResult::Greater));
}

// T5: wide overlapping intervals must NOT be conflated (first-overlap bug guard).
// sqrt(2) and sqrt(3), BOTH given the loose interval [1,2] (overlaps each other).
TEST_CASE("compareRealAlg T5: wide overlapping intervals not conflated") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    UniPolyId xx2 = algebra.allocUni({1, 0, -2});
    UniPolyId xx3 = algebra.allocUni({1, 0, -3});
    RealAlg s2 = algRoot(xx2, 1, mpq_class(1), mpq_class(2));
    RealAlg s3 = algRoot(xx3, 1, mpq_class(1), mpq_class(2));
    // Soundness: must never call them Equal just because intervals overlap.
    CHECK(algebra.compareRealAlg(s2, s3) != CompareResult::Equal);
}
