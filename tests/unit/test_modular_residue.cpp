#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/ModularResidueReasoner.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

namespace {

SatLit rl(SatVar v) { return SatLit::positive(v); }
PolyId var(PolynomialKernel& k, const char* n) { return k.mkVar(k.getOrCreateVar(n)); }
PolyId cst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }
PolyId mul(PolynomialKernel& k, long c, PolyId p) { return k.mul(cst(k, c), p); }

// Build `lo <= v` and `v <= hi` in the normalized Leq form the NIA pipeline
// produces:  (-v + lo) <= 0   and   (v - hi) <= 0.
void addBounds(std::vector<NormalizedNiaConstraint>& cs, PolynomialKernel& k,
               const char* v, long lo, long hi, SatVar loR, SatVar hiR) {
    PolyId vv = var(k, v);
    cs.push_back({k.add(k.neg(vv), cst(k, lo)), Relation::Leq, rl(loR)}); // -v + lo <= 0
    cs.push_back({k.sub(vv, cst(k, hi)), Relation::Leq, rl(hiR)});        //  v - hi <= 0
}

} // namespace

// s = x^2 (mod 4) is always 0 or 1, never 2.  With R := s mod 4 (a div/mod
// group) and the asserted equality R = 2, the system is UNSAT and the only
// free variable is x (enumerated over Z/4).
TEST_CASE("ModularResidue: R = x^2 mod 4, R = 2 -> Conflict") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);

    std::vector<NormalizedNiaConstraint> cs;
    // div/mod group: s - 4*Q - R = 0   (=> s = 4Q + R), 0 <= R <= 3
    cs.push_back({k->sub(k->sub(var(*k, "s"), mul(*k, 4, var(*k, "Q"))), var(*k, "R")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "R", 0, 3, 2, 3);
    // simple def: s - x^2 = 0  (=> s = x^2)
    cs.push_back({k->sub(var(*k, "s"), k->pow(var(*k, "x"), 2)), Relation::Eq, rl(4)});
    // check-only eq: R - 2 = 0
    cs.push_back({k->sub(var(*k, "R"), cst(*k, 2)), Relation::Eq, rl(5)});

    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
    CHECK_FALSE(res.conflict->clause.empty());
}

// Non-power-of-two modulus: R = x^2 mod 3 is always 0 or 1, never 2. With the
// asserted R = 2 the system is UNSAT, free variable x enumerated over Z/3.
// Exercises the relaxed (any n>=2) div-group recognition.
TEST_CASE("ModularResidue: R = x^2 mod 3, R = 2 -> Conflict (non-pow2)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->sub(var(*k, "s"), mul(*k, 3, var(*k, "Q"))), var(*k, "R")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "R", 0, 2, 2, 3);
    cs.push_back({k->sub(var(*k, "s"), k->pow(var(*k, "x"), 2)), Relation::Eq, rl(4)});
    cs.push_back({k->sub(var(*k, "R"), cst(*k, 2)), Relation::Eq, rl(5)});
    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// Same structure but R = 1, which IS reachable (x=1 -> x^2=1 -> R=1).
// Must NOT refute (guards against false UNSAT).
TEST_CASE("ModularResidue: R = x^2 mod 4, R = 1 -> NoChange (satisfiable)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->sub(var(*k, "s"), mul(*k, 4, var(*k, "Q"))), var(*k, "R")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "R", 0, 3, 2, 3);
    cs.push_back({k->sub(var(*k, "s"), k->pow(var(*k, "x"), 2)), Relation::Eq, rl(4)});
    cs.push_back({k->sub(var(*k, "R"), cst(*k, 1)), Relation::Eq, rl(5)});

    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Exact-pinned disequality:  R = x^2 mod 4, R != 0 AND R != 1 is UNSAT
// (x^2 mod 4 in {0,1}). Tests the Neq path on a pinned remainder.
TEST_CASE("ModularResidue: R = x^2 mod 4, R!=0 & R!=1 -> Conflict (Neq path)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->sub(var(*k, "s"), mul(*k, 4, var(*k, "Q"))), var(*k, "R")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "R", 0, 3, 2, 3);
    cs.push_back({k->sub(var(*k, "s"), k->pow(var(*k, "x"), 2)), Relation::Eq, rl(4)});
    cs.push_back({var(*k, "R"), Relation::Neq, rl(5)});                 // R != 0
    cs.push_back({k->sub(var(*k, "R"), cst(*k, 1)), Relation::Neq, rl(6)}); // R != 1

    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// No constant modulus present (pure linear eq) -> nothing to do -> NoChange.
TEST_CASE("ModularResidue: x - y = 0 -> NoChange (no modulus)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(var(*k, "x"), var(*k, "y")), Relation::Eq, rl(1)});
    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// The real modInv8 structure (assert (= 1 (mod (* d inv2) 256)) negated),
// reproduced as the NIA pipeline lowers it. One Newton step gives
// d*inv2 == 1 (mod 256) for every odd d, contradicting r7 != 1 -> UNSAT.
TEST_CASE("ModularResidue: modInv8-shaped system at mod 256 -> Conflict") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;

    auto d   = [&]{ return var(*k, "d"); };
    auto inv0= [&]{ return var(*k, "inv0"); };
    auto inv1= [&]{ return var(*k, "inv1"); };
    auto inv2= [&]{ return var(*k, "inv2"); };

    // r1 = d mod 2 :  d - 2*q0 - r1 = 0, 0<=r1<=1
    cs.push_back({k->sub(k->sub(d(), mul(*k, 2, var(*k, "q0"))), var(*k, "r1")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "r1", 0, 1, 2, 3);
    // check: r1 = 1  (d odd)
    cs.push_back({k->sub(var(*k, "r1"), cst(*k, 1)), Relation::Eq, rl(4)});
    // inv0 = 3*d
    cs.push_back({k->sub(inv0(), mul(*k, 3, d())), Relation::Eq, rl(5)});
    // r3 = inv0 mod 4 : inv0 - 4*q2 - r3 = 0, 0<=r3<=3
    cs.push_back({k->sub(k->sub(inv0(), mul(*k, 4, var(*k, "q2"))), var(*k, "r3")),
                  Relation::Eq, rl(6)});
    addBounds(cs, *k, "r3", 0, 3, 7, 8);
    // r5 = (inv0+2) mod 4 : inv0 + 2 - 4*q4 - r5 = 0, 0<=r5<=3
    cs.push_back({k->sub(k->sub(k->add(inv0(), cst(*k, 2)), mul(*k, 4, var(*k, "q4"))),
                         var(*k, "r5")), Relation::Eq, rl(9)});
    addBounds(cs, *k, "r5", 0, 3, 10, 11);
    // inv1 = 4*q2 + r5
    cs.push_back({k->sub(k->sub(inv1(), mul(*k, 4, var(*k, "q2"))), var(*k, "r5")),
                  Relation::Eq, rl(12)});
    // inv2 = 2*inv1 - d*inv1^2  =>  inv2 - 2*inv1 + d*inv1^2 = 0
    PolyId dInv1sq = k->mul(d(), k->pow(inv1(), 2));
    cs.push_back({k->add(k->sub(inv2(), mul(*k, 2, inv1())), dInv1sq), Relation::Eq, rl(13)});
    // r7 = (d*inv2) mod 256 : d*inv2 - 256*q6 - r7 = 0, 0<=r7<=255
    cs.push_back({k->sub(k->sub(k->mul(d(), inv2()), mul(*k, 256, var(*k, "q6"))),
                         var(*k, "r7")), Relation::Eq, rl(14)});
    addBounds(cs, *k, "r7", 0, 255, 15, 16);
    // negated goal: r7 != 1
    cs.push_back({k->sub(var(*k, "r7"), cst(*k, 1)), Relation::Neq, rl(17)});

    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// Above the modulus cap (2^20 > default 1<<16) -> skipped soundly -> NoChange.
TEST_CASE("ModularResidue: modulus over cap -> NoChange (no crash, no false UNSAT)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;
    const long BIG = 1L << 20;
    // s - BIG*Q - R = 0, 0<=R<BIG ; s = x^2 ; R = 2
    cs.push_back({k->sub(k->sub(var(*k, "s"), mul(*k, BIG, var(*k, "Q"))), var(*k, "R")),
                  Relation::Eq, rl(1)});
    addBounds(cs, *k, "R", 0, BIG - 1, 2, 3);
    cs.push_back({k->sub(var(*k, "s"), k->pow(var(*k, "x"), 2)), Relation::Eq, rl(4)});
    cs.push_back({k->sub(var(*k, "R"), cst(*k, 2)), Relation::Eq, rl(5)});
    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

namespace {
// Faithful mini-modInv: the real seed (inv0 = 3d; inv1 = 4*(inv0 div 4) +
// ((inv0+2) mod 4) via div/mod groups, giving d*inv1 ≡ 1 mod 16), then `steps`
// Newton iterations inv_{i+1} = inv_i*(2 - d*inv_i), d odd, goal d*inv_last mod
// 2^K != forbid. This mirrors the lowered form exactly (unambiguous base).
void buildNewtonChain(std::vector<NormalizedNiaConstraint>& cs, PolynomialKernel& k,
                      int steps, long K, long forbid, SatVar& rsn) {
    auto d = [&]{ return var(k, "d"); };
    // d odd: d - 2*q0 - r1 = 0, 0<=r1<2, r1 = 1
    cs.push_back({k.sub(k.sub(d(), mul(k, 2, var(k, "q0"))), var(k, "r1")), Relation::Eq, rl(rsn++)});
    addBounds(cs, k, "r1", 0, 1, rsn, rsn + 1); rsn += 2;
    cs.push_back({k.sub(var(k, "r1"), cst(k, 1)), Relation::Eq, rl(rsn++)});
    // inv0 = 3d
    cs.push_back({k.sub(var(k, "inv0"), mul(k, 3, d())), Relation::Eq, rl(rsn++)});
    // r3 = inv0 mod 4
    cs.push_back({k.sub(k.sub(var(k, "inv0"), mul(k, 4, var(k, "q2"))), var(k, "r3")), Relation::Eq, rl(rsn++)});
    addBounds(cs, k, "r3", 0, 3, rsn, rsn + 1); rsn += 2;
    // r5 = (inv0+2) mod 4
    cs.push_back({k.sub(k.sub(k.add(var(k, "inv0"), cst(k, 2)), mul(k, 4, var(k, "q4"))), var(k, "r5")),
                  Relation::Eq, rl(rsn++)});
    addBounds(cs, k, "r5", 0, 3, rsn, rsn + 1); rsn += 2;
    // inv1 = 4*q2 + r5  (the seed)
    cs.push_back({k.sub(k.sub(var(k, "inv1"), mul(k, 4, var(k, "q2"))), var(k, "r5")), Relation::Eq, rl(rsn++)});
    // Newton steps inv2 .. inv_{1+steps}
    std::string prev = "inv1";
    for (int i = 2; i <= 1 + steps; ++i) {
        std::string next = "inv" + std::to_string(i);
        PolyId dPrevSq = k.mul(d(), k.pow(var(k, prev.c_str()), 2));
        cs.push_back({k.add(k.sub(var(k, next.c_str()), mul(k, 2, var(k, prev.c_str()))), dPrevSq),
                      Relation::Eq, rl(rsn++)});
        prev = next;
    }
    // goal: d*inv_last - 2^K*qg - rg = 0, 0<=rg<2^K, rg != forbid
    const long M = 1L << K;
    cs.push_back({k.sub(k.sub(k.mul(d(), var(k, prev.c_str())), mul(k, M, var(k, "qg"))), var(k, "rg")),
                  Relation::Eq, rl(rsn++)});
    addBounds(cs, k, "rg", 0, M - 1, rsn, rsn + 1); rsn += 2;
    cs.push_back({k.sub(var(k, "rg"), cst(k, forbid)), Relation::Neq, rl(rsn++)});
}
} // namespace

// 3 Newton steps: base d*x1 = d^2 ≡ 1 (mod 8) for odd d, doubled 3x => mod 2^24.
// Goal modulus 2^24 is past the enum cap, so ONLY Hensel lifting can refute it.
TEST_CASE("ModularResidue: Hensel 3-step Newton chain, d*x4 != 1 mod 2^24 -> Conflict") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;
    SatVar rsn = 1;
    buildNewtonChain(cs, *k, /*steps=*/3, /*K=*/24, /*forbid=*/1, rsn);
    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// rg is forced to 1, so the goal `rg != 2` is satisfiable -> must NOT refute.
// (Hensel's error identity only holds for the forbidden value 1.)
TEST_CASE("ModularResidue: Hensel chain with goal rg != 2 -> NoChange (satisfiable)") {
    auto k = createPolynomialKernel();
    ModularResidueReasoner r(*k);
    std::vector<NormalizedNiaConstraint> cs;
    SatVar rsn = 1;
    buildNewtonChain(cs, *k, /*steps=*/3, /*K=*/24, /*forbid=*/2, rsn);
    auto res = r.run(cs);
    CHECK(res.kind == NiaReasoningKind::NoChange);
}
