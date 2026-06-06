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

// --- Increment #9a: PROPAGATE a congruence through an equality chain ---

// a-b=0, b-c=0, c-3=0  with only  a ≡ 0 (mod 4) given.
// Propagation: a≡0 & a-b=0 => b≡0; b-c=0 => c≡0; then c-3=0 => -3 ≢ 0 (mod 4) => UNSAT.
// (The reasoner must DERIVE b,c's congruences, not just use the handed-in one.)
TEST_CASE("Dio-mod: propagate a≡0 through a=b=c chain, c=3 -> Conflict") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId va = kernel->getOrCreateVar("a"), vb = kernel->getOrCreateVar("b"),
          vc = kernel->getOrCreateVar("c");
    PolyId ab = kernel->sub(kernel->mkVar(va), kernel->mkVar(vb));            // a-b
    PolyId bc = kernel->sub(kernel->mkVar(vb), kernel->mkVar(vc));            // b-c
    PolyId c3 = kernel->sub(kernel->mkVar(vc), pcst(*kernel, 3));             // c-3
    auto res = r.run({{ab, Relation::Eq, mkReason(1)},
                      {bc, Relation::Eq, mkReason(2)},
                      {c3, Relation::Eq, mkReason(3)}},
                     {{va, mpz_class(0), mpz_class(4), mkReason(4)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// Soundness: same chain but c = 4 (≡ 0 mod 4) is consistent -> NoChange.
TEST_CASE("Dio-mod: propagate a≡0 through chain, c=4 -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId va = kernel->getOrCreateVar("a"), vb = kernel->getOrCreateVar("b"),
          vc = kernel->getOrCreateVar("c");
    PolyId ab = kernel->sub(kernel->mkVar(va), kernel->mkVar(vb));
    PolyId bc = kernel->sub(kernel->mkVar(vb), kernel->mkVar(vc));
    PolyId c4 = kernel->sub(kernel->mkVar(vc), pcst(*kernel, 4));
    auto res = r.run({{ab, Relation::Eq, mkReason(1)},
                      {bc, Relation::Eq, mkReason(2)},
                      {c4, Relation::Eq, mkReason(3)}},
                     {{va, mpz_class(0), mpz_class(4), mkReason(4)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}
