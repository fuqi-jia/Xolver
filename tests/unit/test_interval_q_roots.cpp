// Direct tests for the outward-rounded rational sqrt and d-th root.
//
// These are exercised indirectly through RelationContractorQ V2 / V3b,
// but the soundness contract — floor ≤ true ≤ ceil — is load-bearing for
// every narrowing they emit. Pinning the primitive lets us re-tune
// scaleBits or swap mpz backends later without sneaking in regressions.

#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/interval/IntervalQRoots.h"

using namespace xolver;

// Helpers --------------------------------------------------------------------

static mpq_class pow_q(const mpq_class& q, unsigned d) {
    if (d == 0) return mpq_class(1);
    mpq_class r = q;
    for (unsigned i = 1; i < d; ++i) r *= q;
    return r;
}

// Soundness witnesses ---------------------------------------------------------

TEST_CASE("mpqSqrt: floor² ≤ p ≤ ceil² for a sample of nonneg rationals") {
    const mpq_class samples[] = {
        mpq_class(0), mpq_class(1), mpq_class(2), mpq_class(4),
        mpq_class(5), mpq_class(7), mpq_class(100),
        mpq_class(1, 4), mpq_class(3, 7), mpq_class(99, 100),
        mpq_class(123456789, 7),
    };
    for (const auto& p : samples) {
        mpq_class lo = mpqSqrtFloor(p);
        mpq_class hi = mpqSqrtCeil(p);
        CHECK(lo * lo <= p);
        CHECK(hi * hi >= p);
        CHECK(lo <= hi);
    }
}

TEST_CASE("mpqSqrt: exact at perfect squares (within scaleBits headroom)") {
    // 4 = 2², 9 = 3², 25 = 5², 100 = 10². Both bounds should hit exactly.
    const std::pair<mpq_class, mpq_class> exacts[] = {
        {mpq_class(0), mpq_class(0)},
        {mpq_class(1), mpq_class(1)},
        {mpq_class(4), mpq_class(2)},
        {mpq_class(9), mpq_class(3)},
        {mpq_class(25), mpq_class(5)},
        {mpq_class(100), mpq_class(10)},
        // Perfect rational square: (3/2)² = 9/4.
        {mpq_class(9, 4), mpq_class(3, 2)},
    };
    for (const auto& [p, expected] : exacts) {
        mpq_class lo = mpqSqrtFloor(p);
        mpq_class hi = mpqSqrtCeil(p);
        CHECK(lo == expected);
        CHECK(hi == expected);
    }
}

TEST_CASE("mpqSqrt: defensive 0 for negative input (over-approx convention)") {
    CHECK(mpqSqrtFloor(mpq_class(-1)) == mpq_class(0));
    CHECK(mpqSqrtCeil(mpq_class(-1)) == mpq_class(0));
    CHECK(mpqSqrtFloor(mpq_class(-123456)) == mpq_class(0));
}

TEST_CASE("mpqRoot: floor^d ≤ p ≤ ceil^d across d ∈ {2, 3, 4, 5, 7}") {
    const mpq_class samples[] = {
        mpq_class(0), mpq_class(1), mpq_class(2), mpq_class(7),
        mpq_class(8), mpq_class(27), mpq_class(64),
        mpq_class(1, 3), mpq_class(5, 7), mpq_class(10000),
    };
    for (unsigned d : {2u, 3u, 4u, 5u, 7u}) {
        for (const auto& p : samples) {
            mpq_class lo = mpqRootFloor(p, d);
            mpq_class hi = mpqRootCeil(p, d);
            CHECK(pow_q(lo, d) <= p);
            CHECK(pow_q(hi, d) >= p);
            CHECK(lo <= hi);
        }
    }
}

TEST_CASE("mpqRoot: exact at perfect d-th powers") {
    // d=3: 8 = 2³, 27 = 3³, 64 = 4³.
    CHECK(mpqRootFloor(mpq_class(8), 3) == mpq_class(2));
    CHECK(mpqRootCeil(mpq_class(8), 3) == mpq_class(2));
    CHECK(mpqRootFloor(mpq_class(27), 3) == mpq_class(3));
    CHECK(mpqRootCeil(mpq_class(27), 3) == mpq_class(3));
    CHECK(mpqRootFloor(mpq_class(64), 3) == mpq_class(4));

    // d=4: 16 = 2⁴, 81 = 3⁴.
    CHECK(mpqRootFloor(mpq_class(16), 4) == mpq_class(2));
    CHECK(mpqRootCeil(mpq_class(16), 4) == mpq_class(2));
    CHECK(mpqRootFloor(mpq_class(81), 4) == mpq_class(3));

    // d=5: 32 = 2⁵.
    CHECK(mpqRootFloor(mpq_class(32), 5) == mpq_class(2));
    CHECK(mpqRootCeil(mpq_class(32), 5) == mpq_class(2));
}

TEST_CASE("mpqRoot: d == 1 is the identity") {
    const mpq_class samples[] = {
        mpq_class(0), mpq_class(7), mpq_class(-3),
        mpq_class(5, 11), mpq_class(-9, 4),
    };
    for (const auto& p : samples) {
        CHECK(mpqRootFloor(p, 1) == p);
        CHECK(mpqRootCeil(p, 1) == p);
    }
}

TEST_CASE("mpqRoot: d == 2 matches the dedicated sqrt path") {
    // The implementation routes d == 2 through mpqSqrt*, so consistency is
    // structural — but pinning it guards against future divergence.
    const mpq_class samples[] = {
        mpq_class(2), mpq_class(7), mpq_class(100),
        mpq_class(3, 7), mpq_class(99, 100),
    };
    for (const auto& p : samples) {
        CHECK(mpqRootFloor(p, 2) == mpqSqrtFloor(p));
        CHECK(mpqRootCeil(p, 2) == mpqSqrtCeil(p));
    }
}

TEST_CASE("mpqRoot: defensive 0 for negative input (use sign-flip at callsite)") {
    // The helpers don't reach into odd-d negative-input handling — callers
    // are expected to compute -mpqRootFloor(-T, d) / -mpqRootCeil(-T, d)
    // explicitly. The helpers themselves return 0 for negative input.
    CHECK(mpqRootFloor(mpq_class(-8), 3) == mpq_class(0));
    CHECK(mpqRootCeil(mpq_class(-8), 3) == mpq_class(0));
    CHECK(mpqRootFloor(mpq_class(-16), 4) == mpq_class(0));
}

TEST_CASE("mpqRoot: outward irrational — 2^(1/3) and 3^(1/4) bracket correctly") {
    // 2^(1/3) ≈ 1.2599; floor ≤ 2^(1/3) ≤ ceil with both bounds rational.
    mpq_class loCbrt2 = mpqRootFloor(mpq_class(2), 3);
    mpq_class hiCbrt2 = mpqRootCeil(mpq_class(2), 3);
    CHECK(pow_q(loCbrt2, 3) <= mpq_class(2));
    CHECK(pow_q(hiCbrt2, 3) >= mpq_class(2));
    // Sanity bands: 1 ≤ 2^(1/3) ≤ 2.
    CHECK(loCbrt2 >= mpq_class(1));
    CHECK(hiCbrt2 <= mpq_class(2));

    // 3^(1/4) ≈ 1.3161.
    mpq_class lo3_4 = mpqRootFloor(mpq_class(3), 4);
    mpq_class hi3_4 = mpqRootCeil(mpq_class(3), 4);
    CHECK(pow_q(lo3_4, 4) <= mpq_class(3));
    CHECK(pow_q(hi3_4, 4) >= mpq_class(3));
}

TEST_CASE("mpqRoot: rational radicand (5/7)^(1/3) preserves the contract") {
    mpq_class p(5, 7);
    mpq_class lo = mpqRootFloor(p, 3);
    mpq_class hi = mpqRootCeil(p, 3);
    CHECK(pow_q(lo, 3) <= p);
    CHECK(pow_q(hi, 3) >= p);
    CHECK(lo > mpq_class(0));
    CHECK(hi < mpq_class(1));  // (5/7) < 1, so its cube root < 1.
}

TEST_CASE("mpqSqrt/Root: scaleBits raises precision without breaking soundness") {
    // Soundness is invariant — only tightness changes.
    mpq_class p(7);
    for (unsigned k : {1u, 4u, 16u, 32u, 64u}) {
        mpq_class lo = mpqSqrtFloor(p, k);
        mpq_class hi = mpqSqrtCeil(p, k);
        CHECK(lo * lo <= p);
        CHECK(hi * hi >= p);
    }
    for (unsigned k : {1u, 4u, 16u, 32u, 64u}) {
        mpq_class lo = mpqRootFloor(p, 3, k);
        mpq_class hi = mpqRootCeil(p, 3, k);
        CHECK(pow_q(lo, 3) <= p);
        CHECK(pow_q(hi, 3) >= p);
    }
}
