#include <doctest/doctest.h>
#include "theory/core/DerivedFact.h"
#include <gmpxx.h>

// Tests for IntervalSet::integerPointCount() — the O(#intervals), no-materialization
// counterpart of integerPoints().  The hard contract is that, for any finite-Int set,
//     integerPointCount() == integerPoints().size()
// including across overlapping / touching / open-endpoint / rational-endpoint cases
// (where shared integers must be counted exactly once, matching integerPoints()'s
// sort+unique).  This equivalence is what lets the NIA finite-domain enumerator
// size-gate a domain BEFORE paying the O(range) materialization.

using namespace xolver;

namespace {

Interval mkIv(const mpq_class& lo, bool loOpen, const mpq_class& hi, bool hiOpen) {
    Interval iv;
    iv.lower = BoundEndpoint::rational(lo); iv.lowerOpen = loOpen;
    iv.upper = BoundEndpoint::rational(hi); iv.upperOpen = hiOpen;
    return iv;
}

IntervalSet intSet(std::vector<Interval> ivs) {
    IntervalSet s(IntervalSet::Domain::Int);
    s.intervals = std::move(ivs);
    return s;
}

// The equivalence the size-gate relies on.
void checkEquiv(const IntervalSet& s) {
    const mpz_class cnt = s.integerPointCount();
    const mpz_class mat = mpz_class(s.integerPoints().size());
    CHECK(cnt == mat);
}

}  // namespace

TEST_CASE("integerPointCount: single closed interval") {
    auto s = intSet({mkIv(2, false, 5, false)});   // {2,3,4,5}
    CHECK(s.integerPointCount() == 4);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: open endpoints drop the boundary integers") {
    auto s = intSet({mkIv(2, true, 5, true)});      // (2,5) -> {3,4}
    CHECK(s.integerPointCount() == 2);
    checkEquiv(s);

    auto half = intSet({mkIv(2, true, 5, false)});  // (2,5] -> {3,4,5}
    CHECK(half.integerPointCount() == 3);
    checkEquiv(half);
}

TEST_CASE("integerPointCount: rational endpoints use ceil(lo)/floor(hi)") {
    // [1/2, 7/2] -> integers 1,2,3
    auto s = intSet({mkIv(mpq_class(1, 2), false, mpq_class(7, 2), false)});
    CHECK(s.integerPointCount() == 3);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: overlapping intervals count shared integers once") {
    // [1,4] U [3,6] -> {1,2,3,4,5,6} = 6, NOT 4+4=8
    auto s = intSet({mkIv(1, false, 4, false), mkIv(3, false, 6, false)});
    CHECK(s.integerPointCount() == 6);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: intervals sharing exactly one integer merge to a union") {
    // [1,3] U [3,5] -> {1,2,3,4,5} = 5 (integer 3 shared, counted once)
    auto s = intSet({mkIv(1, false, 3, false), mkIv(3, false, 5, false)});
    CHECK(s.integerPointCount() == 5);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: disjoint intervals sum separately") {
    // [1,3] U [5,7] -> 3 + 3 = 6 (gap at 4 keeps them apart)
    auto s = intSet({mkIv(1, false, 3, false), mkIv(5, false, 7, false)});
    CHECK(s.integerPointCount() == 6);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: empty/degenerate interval has no integers") {
    auto s = intSet({mkIv(5, false, 2, false)});    // hi < lo -> no integer points
    CHECK(s.integerPointCount() == 0);
    checkEquiv(s);

    auto openPoint = intSet({mkIv(3, true, 3, true)});  // (3,3) -> empty
    CHECK(openPoint.integerPointCount() == 0);
    checkEquiv(openPoint);
}

TEST_CASE("integerPointCount: out-of-order intervals are handled (internal sort)") {
    // Same union as the overlap case, but pushed in reverse order.
    auto s = intSet({mkIv(3, false, 6, false), mkIv(1, false, 4, false)});
    CHECK(s.integerPointCount() == 6);
    checkEquiv(s);
}

TEST_CASE("integerPointCount: huge domain is counted WITHOUT materializing") {
    // The whole purpose: a domain far past the enumerator's 4096 gate must cost
    // O(1) to size.  We assert the exact count but deliberately do NOT call
    // integerPoints() (which would materialize a million mpz_class values).
    auto s = intSet({mkIv(0, false, 1000000, false)});  // {0..1000000} = 1000001
    CHECK(s.integerPointCount() == 1000001);
    CHECK(s.integerPointCount() > 4096);                // would trip the gate
}

TEST_CASE("integerPointCount: non-finite (unbounded) set returns 0, matching integerPoints") {
    // [0, +Inf) over Int is NOT isFiniteInt() -> both report 'no enumerable points'.
    IntervalSet s(IntervalSet::Domain::Int);
    Interval iv;
    iv.lower = BoundEndpoint::rational(mpq_class(0)); iv.lowerOpen = false;
    iv.upper = BoundEndpoint::posInf();               iv.upperOpen = true;
    s.intervals.push_back(iv);
    CHECK_FALSE(s.isFiniteInt());
    CHECK(s.integerPointCount() == 0);
    CHECK(s.integerPoints().empty());
}

TEST_CASE("integerPointCount: empty set is finite with zero points") {
    auto s = intSet({});
    CHECK(s.isFiniteInt());
    CHECK(s.integerPointCount() == 0);
    checkEquiv(s);
}
