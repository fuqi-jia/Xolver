// CAC engine (module C — get_unsat_cover). End-to-end: 1- and 2-variable SAT
// and UNSAT QF_NRA problems solved by conflict-driven coverings (no full
// closure). SAT status means the engine found a full sample validating every
// constraint (its leaf check); UNSAT means a gap-free covering.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/cac/CacEngine.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"
#endif

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

static RationalPolynomial K(long c) { return RationalPolynomial::fromConstant(mpq_class(c)); }

TEST_CASE("CAC engine: 1-var UNSAT x^2 < 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial xx; xx.addVar(x, 2, 1); xx.normalize();          // x^2
    CacEngine eng(&backend, kernel.get(), {x}, {{xx, Relation::Lt}});   // x^2 < 0
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 1-var UNSAT  x>2 and x<1") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial a; a.addVar(x, 1, 1); a = a + K(-2); a.normalize();   // x - 2
    RationalPolynomial b; b.addVar(x, 1, 1); b = b + K(-1); b.normalize();   // x - 1
    CacEngine eng(&backend, kernel.get(), {x},
                  {{a, Relation::Gt}, {b, Relation::Lt}});                  // x>2 ∧ x<1
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 1-var SAT  x^2 < 4 and x > 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial a; a.addVar(x, 2, 1); a = a + K(-4); a.normalize();   // x^2 - 4
    RationalPolynomial b; b.addVar(x, 1, 1); b.normalize();                  // x
    CacEngine eng(&backend, kernel.get(), {x},
                  {{a, Relation::Lt}, {b, Relation::Gt}});                  // x^2<4 ∧ x>0
    CHECK(eng.solve().status == CacStatus::Sat);
}

TEST_CASE("CAC engine: 2-var UNSAT  x^2+y^2 < 1 and x > 2") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-1); circ.normalize();                                   // x^2+y^2-1
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg = xg + K(-2); xg.normalize(); // x-2
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}});
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 2-var SAT  x^2+y^2 < 4 and x > 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-4); circ.normalize();                                   // x^2+y^2-4
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg.normalize();               // x
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}});
    CHECK(eng.solve().status == CacStatus::Sat);
}

#endif  // XOLVER_HAS_LIBPOLY
