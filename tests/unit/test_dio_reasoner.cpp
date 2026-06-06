#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/DioReasoner.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }
static PolyId pcst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }
static PolyId pscaled(PolynomialKernel& k, long c, PolyId p) { return k.mul(pcst(k, c), p); }

static const char* TWO32 = "4294967296";  // 2^32 — far above ModularResidueReasoner's 2^18 cap

// x - y - 3 = 0  with  x ≡ 0 (mod 2^32) and y ≡ 0 (mod 2^32)  forces
// (0 - 0 - 3) ≡ 0 (mod 2^32), i.e. -3 ≡ 0 (mod 2^32): false => UNSAT.
// ModularResidueReasoner cannot ENUMERATE mod 2^32; this is symbolic.
TEST_CASE("Dio-mod: x-y-3=0 with x,y ≡0 mod 2^32 -> Conflict (symbolic, large modulus)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy)), pcst(*kernel, 3));
    mpz_class m(TWO32);
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), m, mkReason(2)},
                      {vy, mpz_class(0), m, mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// With coefficients: 2x - y - 1 = 0, x,y ≡ 0 (mod 4) -> (0 - 0 - 1) = -1 ≢ 0 (mod 4) => Conflict.
TEST_CASE("Dio-mod: 2x-y-1=0 with x,y ≡0 mod 4 -> Conflict") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(pscaled(*kernel, 2, kernel->mkVar(vx)), kernel->mkVar(vy)),
                           pcst(*kernel, 1));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(4), mkReason(2)},
                      {vy, mpz_class(0), mpz_class(4), mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// Soundness: a satisfiable modular system must NOT refute.
// x - y = 0 with x,y ≡ 0 (mod 4) -> 0 ≡ 0 (mod 4): consistent => NoChange.
TEST_CASE("Dio-mod: x-y=0 with x,y ≡0 mod 4 -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(4), mkReason(2)},
                      {vy, mpz_class(0), mpz_class(4), mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Soundness: if a variable lacks a congruence the equality cannot be reduced
// (slack remains) -> NoChange.  x - y - 3 = 0 with only x ≡ 0 (mod 2^32).
TEST_CASE("Dio-mod: missing congruence -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy)), pcst(*kernel, 3));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(TWO32), mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}
