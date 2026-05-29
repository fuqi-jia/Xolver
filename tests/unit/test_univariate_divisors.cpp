#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"
#include <gmpxx.h>

// Direct tests for UnivariateIntegerReasoner::completeDivisors — the RRT divisor
// enumerator. Prime factorization is the SOLE path (the O(sqrt n) trial-division
// cap is dissolved): 2^256 -> {2:256} -> 257 divisors instantly. The SOUNDNESS
// contract is complete=true IFF the FULL divisor set was enumerated — verified
// below for the un-factorable and over-cap cases.

using namespace xolver;

namespace {
mpz_class pow2(unsigned e) { mpz_class r = 1; r <<= e; return r; }
}

TEST_CASE("completeDivisors: enumerates 12 fully") {
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(12, complete);
    CHECK(complete);
    // ±{1,2,3,4,6,12} = 12 entries
    CHECK(d.size() == 12);
    for (long v : {1, 2, 3, 4, 6, 12}) {
        CHECK(d.count(mpz_class(v)) == 1);
        CHECK(d.count(mpz_class(-v)) == 1);
    }
    CHECK(d.count(mpz_class(5)) == 0);
}

TEST_CASE("completeDivisors: 360 = 2^3*3^2*5 -> 24 divisors fully") {
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(360, complete);
    CHECK(complete);
    CHECK(d.size() == 24u * 2u);  // 24 positive divisors, ±
    CHECK(d.count(mpz_class(360)) == 1);
    CHECK(d.count(mpz_class(7)) == 0);
}

TEST_CASE("completeDivisors: finishes on 2^256 (trial division would hang)") {
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(pow2(256), complete);
    CHECK(complete);
    // divisors of 2^256 are exactly ±2^k for k in [0,256] => 257*2 entries
    CHECK(d.size() == 257u * 2u);
    CHECK(d.count(pow2(128)) == 1);   // sqrt(2^256), the interesting root
    CHECK(d.count(pow2(256)) == 1);
    CHECK(d.count(mpz_class(1)) == 1);
    CHECK(d.count(mpz_class(3)) == 0);  // 3 does not divide a power of 2
}

TEST_CASE("completeDivisors: signals incomplete on large semiprime") {
    // p, q both prime and above the 10^7 trial bound => the bounded trial loop
    // cannot split the product, and it is composite (not accepted as prime) =>
    // complete=false. A partial divisor set must NEVER be reported as complete.
    mpz_class p("1000000007"), q("1000000009");  // both prime, both > 10^7
    bool complete = true;
    auto d = UnivariateIntegerReasoner::completeDivisors(p * q, complete);
    CHECK_FALSE(complete);
    CHECK(d.empty());
}

TEST_CASE("completeDivisors: signals incomplete when over divisor cap") {
    // 2^20000 has 20001 positive divisors, above the 10000 cap => incomplete.
    // (The divisor-count is checked BEFORE enumeration, so this bails fast.)
    bool complete = true;
    auto d = UnivariateIntegerReasoner::completeDivisors(pow2(20000), complete);
    CHECK_FALSE(complete);
    CHECK(d.empty());
}

TEST_CASE("completeDivisors: accepts a single large prime") {
    // A prime above 10^6: bounded trial finds no factor, residual < B^2 => prime,
    // divisors are just ±1, ±p. Complete.
    mpz_class p("1000003");  // prime, > 10^6, < 10^14 = B^2
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(p, complete);
    CHECK(complete);
    CHECK(d.size() == 4);
    CHECK(d.count(mpz_class(1)) == 1);
    CHECK(d.count(p) == 1);
    CHECK(d.count(-p) == 1);
}
