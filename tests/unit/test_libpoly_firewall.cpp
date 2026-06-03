// libpoly heap-corruption firewall (LibpolyBackend).
//
// Root cause (gdb-verified 2026-06-03): libpoly's isolate_real_roots / sgn, when
// it substitutes a large coordinate into a high-degree term, builds multi-megabit
// exact-rational coefficients; GMP overflows an internal size field and free()s a
// bogus pointer => glibc SIGABRT "double free or corruption" (NOT a SIGSEGV, so the
// sigsetjmp recovery harness cannot catch it). These functions are SHARED with
// CDCAC, so the corruption is a CDCAC bug, not just an nlsat one.
//
// The firewall refuses any libpoly isolation/sgn whose substituted-coefficient
// bit-magnitude exceeds XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS, bailing as
// crashOccurred (callers treat it as inconclusive => Unknown, never as "0 roots").
// Such inputs are doubly-exponential and infeasible regardless. These tests pin
// (a) the firewall does NOT interfere with normal, modest isolation, and (b) it
// bails gracefully (no crash/abort) on a pathological high-degree × huge-coordinate
// input — the exact shape that corrupts the heap without the guard.

#include <doctest/doctest.h>
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>

using namespace xolver;

TEST_CASE("libpoly firewall: modest substitution still isolates normally") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");

    // p = y - x ; with x = 3 the single real root in y is 3.
    PolyId p = kernel->add(kernel->mkVar(y), kernel->neg(kernel->mkVar(x)));
    SamplePoint prefix;
    prefix.push(x, RealAlg::fromRational(mpq_class(3)));

    RootSet rs = algebra.isolateRealRootsAlgebraic(p, prefix, y);
    CHECK_FALSE(rs.crashOccurred);   // firewall must not fire on a tiny coordinate
    CHECK(rs.numRoots() == 1);
}

TEST_CASE("libpoly firewall: oversize substituted coefficient bails (no heap corruption)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");

    // p = x^16 * y + 1.  Substituting a huge x makes the y-coefficient ~16*bits(x),
    // i.e. multi-Kbit — the exact shape (high degree in a prefix var × large
    // coordinate) that corrupts libpoly's root isolation. x = 2^60000 (60001 bits)
    // => estimated coeff ~ 960016 bits, far above the 262144-bit default ceiling.
    PolyId p = kernel->add(
        kernel->mul(kernel->pow(kernel->mkVar(x), 16), kernel->mkVar(y)),
        kernel->mkConst(mpq_class(1)));

    mpz_class big;
    mpz_ui_pow_ui(big.get_mpz_t(), 2, 60000);   // 2^60000
    SamplePoint prefix;
    prefix.push(x, RealAlg::fromRational(mpq_class(big)));

    // Must return gracefully (the process must NOT abort) and signal inconclusive.
    RootSet rs = algebra.isolateRealRootsAlgebraic(p, prefix, y);
    CHECK(rs.crashOccurred);
    CHECK(rs.numRoots() == 0);
}
