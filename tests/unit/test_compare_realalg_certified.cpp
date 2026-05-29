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
