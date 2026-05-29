#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"
#include <cstdlib>
#include <gmpxx.h>

// Direct tests for UnivariateIntegerReasoner::completeDivisors — the RRT divisor
// enumerator. Default mode = O(sqrt n) trial division behind the infeasibility
// cap; XOLVER_NIA_DIVISOR_FACTOR = prime-factorization enumeration that finishes
// fast on huge-but-factorable constants (EVM mod-2^256). The SOUNDNESS contract
// is complete=true IFF the full divisor set was enumerated — verified below for
// the un-factorable and over-cap cases.

using namespace xolver;

namespace {
mpz_class pow2(unsigned e) { mpz_class r = 1; r <<= e; return r; }
}

TEST_CASE("completeDivisors: default mode enumerates 12 fully") {
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
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

TEST_CASE("completeDivisors: factor mode matches default on small composite") {
    bool cDef = false, cFac = false;
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    auto def = UnivariateIntegerReasoner::completeDivisors(360, cDef);
    setenv("XOLVER_NIA_DIVISOR_FACTOR", "1", 1);
    auto fac = UnivariateIntegerReasoner::completeDivisors(360, cFac);
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    CHECK(cDef);
    CHECK(cFac);
    CHECK(def == fac);  // identical divisor sets, two algorithms
}

TEST_CASE("completeDivisors: factor mode finishes on 2^256 (default would hang)") {
    setenv("XOLVER_NIA_DIVISOR_FACTOR", "1", 1);
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(pow2(256), complete);
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    CHECK(complete);
    // divisors of 2^256 are exactly ±2^k for k in [0,256] => 257*2 entries
    CHECK(d.size() == 257u * 2u);
    CHECK(d.count(pow2(128)) == 1);   // sqrt(2^256), the interesting root
    CHECK(d.count(pow2(256)) == 1);
    CHECK(d.count(mpz_class(1)) == 1);
    CHECK(d.count(mpz_class(3)) == 0);  // 3 does not divide a power of 2
}

TEST_CASE("completeDivisors: factor mode signals incomplete on large semiprime") {
    // p, q both prime and above the 10^7 trial bound => the bounded trial loop
    // cannot split the product, and it is composite (not accepted as prime) =>
    // complete=false. A partial divisor set must NEVER be reported as complete.
    mpz_class p("1000000007"), q("1000000009");  // both prime, both > 10^7
    setenv("XOLVER_NIA_DIVISOR_FACTOR", "1", 1);
    bool complete = true;
    auto d = UnivariateIntegerReasoner::completeDivisors(p * q, complete);
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    CHECK_FALSE(complete);
    CHECK(d.empty());
}

TEST_CASE("completeDivisors: factor mode signals incomplete when over divisor cap") {
    // 2^20000 has 20001 positive divisors, above the 10000 cap => incomplete.
    // (The divisor-count is checked BEFORE enumeration, so this bails fast.)
    setenv("XOLVER_NIA_DIVISOR_FACTOR", "1", 1);
    bool complete = true;
    auto d = UnivariateIntegerReasoner::completeDivisors(pow2(20000), complete);
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    CHECK_FALSE(complete);
    CHECK(d.empty());
}

TEST_CASE("completeDivisors: factor mode accepts a single large prime") {
    // A prime above 10^6: bounded trial finds no factor, residual < B^2 => prime,
    // divisors are just ±1, ±p. Complete.
    mpz_class p("1000003");  // prime, > 10^6, < 10^12 = B^2
    setenv("XOLVER_NIA_DIVISOR_FACTOR", "1", 1);
    bool complete = false;
    auto d = UnivariateIntegerReasoner::completeDivisors(p, complete);
    unsetenv("XOLVER_NIA_DIVISOR_FACTOR");
    CHECK(complete);
    CHECK(d.size() == 4);
    CHECK(d.count(mpz_class(1)) == 1);
    CHECK(d.count(p) == 1);
    CHECK(d.count(-p) == 1);
}
