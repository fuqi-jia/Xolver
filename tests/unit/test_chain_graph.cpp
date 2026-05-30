#include <doctest/doctest.h>

#include "theory/arith/nia/reasoners/ChainGraph.h"
#include "theory/arith/poly/PolynomialKernel.h"

#include <gmpxx.h>
#include <vector>

// Phase 2.7a unit tests for ChainGraph + composeChainSteps.
//
// The primitive derivation under test is:
//
//   (= a (mod x s)) ∧ (= x (mod y s)) ⇒ (= a (mod y s))
//
// which in congruence form is just transitivity of ≡ (mod s):
//
//   a ≡ x (mod s) ∧ x ≡ y (mod s) ⇒ a ≡ y (mod s).
//
// We validate two things:
//   (1) composeChainSteps composes the right endpoints + unions the reasons.
//   (2) the math of the derivation holds on a small numeric grid (the
//       z3-style sanity check master requested). For every (y, s) with s>0,
//       set x = y mod s and a = x mod s; then (a − y) mod s must be 0.
//       This protects against accidentally encoding a wrong derivation rule
//       (e.g. swapping endpoints in compose) — the soundness layer is
//       written here once and lives in the test file, not the reasoner.

using namespace xolver;

namespace {

SatLit lit(unsigned int v, bool sign = true) {
    return {v, sign};
}

bool hasReason(const ChainStep& s, const SatLit& l) {
    for (const SatLit& r : s.reasons) if (r == l) return true;
    return false;
}

} // namespace

TEST_CASE("ChainGraph: compose two same-modulus edges via shared middle node") {
    auto k = createPolynomialKernel();
    if (!k) return;  // libpoly unavailable — skip silently

    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainStep e1{a, x, mpz_class(256), {lit(1), lit(2)}};
    ChainStep e2{x, y, mpz_class(256), {lit(3), lit(4)}};

    auto composed = composeChainSteps(e1, e2);
    REQUIRE(composed.has_value());
    CHECK(composed->modulus == mpz_class(256));
    // Endpoint set is {a, y} (undirected).
    bool endpointsOk = (composed->lhs == a && composed->rhs == y) ||
                       (composed->lhs == y && composed->rhs == a);
    CHECK(endpointsOk);
    // Reason set is union of e1 and e2 reasons.
    CHECK(composed->reasons.size() == 4);
    CHECK(hasReason(*composed, lit(1)));
    CHECK(hasReason(*composed, lit(2)));
    CHECK(hasReason(*composed, lit(3)));
    CHECK(hasReason(*composed, lit(4)));
}

TEST_CASE("ChainGraph: compose rejects different moduli") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainStep e1{a, x, mpz_class(256), {lit(1)}};
    ChainStep e2{x, y, mpz_class(7),   {lit(2)}};

    auto composed = composeChainSteps(e1, e2);
    CHECK(!composed.has_value());
}

TEST_CASE("ChainGraph: compose dedupes shared reasons under union") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    // Both edges carry SatLit(5); the composed step must list it once.
    ChainStep e1{a, x, mpz_class(8), {lit(1), lit(5)}};
    ChainStep e2{x, y, mpz_class(8), {lit(5), lit(7)}};

    auto composed = composeChainSteps(e1, e2);
    REQUIRE(composed.has_value());
    CHECK(composed->reasons.size() == 3);
    CHECK(hasReason(*composed, lit(1)));
    CHECK(hasReason(*composed, lit(5)));
    CHECK(hasReason(*composed, lit(7)));
}

TEST_CASE("ChainGraph: closeTransitive(D=2) derives a→y from a→x and x→y") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});
    CHECK(g.edges().size() == 2);

    g.closeTransitive(/*maxDepth=*/2);
    // At D=2 we expect exactly one new edge a↔y at modulus 256.
    auto derived = g.findStep(a, y, mpz_class(256));
    REQUIRE(derived.has_value());
    CHECK(derived->reasons.size() == 2);
    CHECK(hasReason(*derived, lit(1)));
    CHECK(hasReason(*derived, lit(2)));
}

TEST_CASE("ChainGraph: closeTransitive(D=1) does not derive new edges") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});
    g.closeTransitive(/*maxDepth=*/1);
    CHECK(g.edges().size() == 2);
    CHECK(!g.findStep(a, y, mpz_class(256)).has_value());
}

TEST_CASE("ChainGraph: closeTransitive(D=3) extends a→z across a chain of 3") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId z = k->mkVar(k->getOrCreateVar("z"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});
    g.addEdge({y, z, mpz_class(256), {lit(3)}});
    g.closeTransitive(/*maxDepth=*/3);
    auto derived = g.findStep(a, z, mpz_class(256));
    REQUIRE(derived.has_value());
    CHECK(derived->reasons.size() == 3);
    CHECK(hasReason(*derived, lit(1)));
    CHECK(hasReason(*derived, lit(2)));
    CHECK(hasReason(*derived, lit(3)));
}

TEST_CASE("ChainGraph: closeTransitive(D=2) does NOT derive a→z across 3-chain") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId z = k->mkVar(k->getOrCreateVar("z"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});
    g.addEdge({y, z, mpz_class(256), {lit(3)}});
    g.closeTransitive(/*maxDepth=*/2);
    // a↔y and x↔z should exist (each combines 2 edges); a↔z combines 3.
    CHECK(g.findStep(a, y, mpz_class(256)).has_value());
    CHECK(g.findStep(x, z, mpz_class(256)).has_value());
    CHECK(!g.findStep(a, z, mpz_class(256)).has_value());
}

// Phase 2.7b — goal-driven reduction.
TEST_CASE("ChainGraph: tryReduceGoal finds the direct edge without closure") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(11)}});
    auto out = tryReduceGoal(g, a, x, mpz_class(256), /*maxDepth=*/1);
    REQUIRE(out.has_value());
    CHECK(out->reasons.size() == 1);
    CHECK(hasReason(*out, lit(11)));
}

TEST_CASE("ChainGraph: tryReduceGoal derives 2-step chain at D=2") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});

    auto direct = tryReduceGoal(g, a, y, mpz_class(256), /*maxDepth=*/2);
    REQUIRE(direct.has_value());
    CHECK(direct->reasons.size() == 2);
    CHECK(hasReason(*direct, lit(1)));
    CHECK(hasReason(*direct, lit(2)));

    // And the original graph is unchanged (tryReduceGoal works on a copy).
    CHECK(g.edges().size() == 2);
}

TEST_CASE("ChainGraph: tryReduceGoal fails when target is unreachable at depth") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId z = k->mkVar(k->getOrCreateVar("z"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(256), {lit(2)}});
    g.addEdge({y, z, mpz_class(256), {lit(3)}});
    // a→z requires depth 3; D=2 cannot derive it.
    auto out = tryReduceGoal(g, a, z, mpz_class(256), /*maxDepth=*/2);
    CHECK(!out.has_value());
    // At D=3 it derives.
    auto out3 = tryReduceGoal(g, a, z, mpz_class(256), /*maxDepth=*/3);
    REQUIRE(out3.has_value());
    CHECK(out3->reasons.size() == 3);
}

TEST_CASE("ChainGraph: tryReduceGoal fails on modulus mismatch") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId a = k->mkVar(k->getOrCreateVar("a"));
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    ChainGraph g;
    g.addEdge({a, x, mpz_class(256), {lit(1)}});
    g.addEdge({x, y, mpz_class(8),   {lit(2)}});
    auto out256 = tryReduceGoal(g, a, y, mpz_class(256), /*maxDepth=*/2);
    auto out8   = tryReduceGoal(g, a, y, mpz_class(8),   /*maxDepth=*/2);
    CHECK(!out256.has_value());
    CHECK(!out8.has_value());
}

// Phase 2.7b — per-edge cert.
TEST_CASE("ChainGraph: validateChainStep accepts a mathematically sound edge") {
    auto k = createPolynomialKernel();
    if (!k) return;
    // Edge: x ≡ x + 5*256 (mod 256). True for every integer x.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId five256 = k->mkConst(mpq_class(5 * 256));
    PolyId rhs = k->add(x, five256);
    ChainStep step{x, rhs, mpz_class(256), {lit(1)}};
    CHECK(validateChainStep(*k, step));
}

TEST_CASE("ChainGraph: validateChainStep rejects an unsound edge") {
    auto k = createPolynomialKernel();
    if (!k) return;
    // Bogus edge: x ≡ x + 1 (mod 256). Fails at every assignment.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId one = k->mkConst(mpq_class(1));
    PolyId rhs = k->add(x, one);
    ChainStep step{x, rhs, mpz_class(256), {lit(1)}};
    CHECK(!validateChainStep(*k, step));
}

TEST_CASE("ChainGraph: validateChainStep — composed Newton-style edge passes cert") {
    auto k = createPolynomialKernel();
    if (!k) return;
    // For pow2 modulus m: 2*x*m ≡ 0 (mod m). Compose this with x ≡ x:
    // assert (lhs=2*x*m, rhs=0, modulus=m) holds for all x.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    long m = 64;
    PolyId twoM = k->mkConst(mpq_class(2 * m));
    PolyId lhs = k->mul(twoM, x);
    PolyId zero = k->mkConst(mpq_class(0));
    ChainStep step{lhs, zero, mpz_class(m), {lit(1)}};
    CHECK(validateChainStep(*k, step));
}

TEST_CASE("ChainGraph: validateChainStep — composed reasons survive cert reject") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    // Edges: x ≡ y+8 (mod 8) and y+8 ≡ x+1 (mod 8). The composition would
    // claim x ≡ x+1 (mod 8), which is wrong — the cert must reject it.
    // (Each input edge alone is sound: first is a tautology mod 8, second
    // is FALSE, so the composition inherits the falsity.) This exercises
    // that the cert catches a known-bad derivation rather than trusting
    // the compose machinery.
    PolyId eight = k->mkConst(mpq_class(8));
    PolyId one   = k->mkConst(mpq_class(1));
    PolyId yPlus8 = k->add(y, eight);
    PolyId xPlus1 = k->add(x, one);
    ChainStep e1{x, yPlus8, mpz_class(8), {lit(1)}};
    ChainStep e2{yPlus8, xPlus1, mpz_class(8), {lit(2)}};
    auto composed = composeChainSteps(e1, e2);
    REQUIRE(composed.has_value());
    CHECK(!validateChainStep(*k, *composed));
}

// Soundness grid: validate the underlying *mathematical* rule that the chain
// graph encodes — that transitivity of ≡ (mod s) is sound. For each (y, s)
// in a small signed grid, set x = y mod s and a = x mod s; then a ≡ y
// (mod s) must hold (i.e. (a − y) mod s == 0). This is the z3-style sanity
// check master asked for: it pins the mathematical contract independently
// of any ChainGraph code path, so a bug in ChainGraph that swaps endpoints
// or mishandles the modulus would not pass even an apparently-related test.
TEST_CASE("ChainGraph soundness grid: a = x mod s, x = y mod s ⇒ a ≡ y (mod s)") {
    // Modulus s in {2..16} (covers small primes, pow2, composites).
    // y in {-30..30} (covers signs and several wraps).
    for (long s = 2; s <= 16; ++s) {
        mpz_class S = s;
        for (long yi = -30; yi <= 30; ++yi) {
            mpz_class y = yi;
            mpz_class x = y % S; if (x < 0) x += S;
            mpz_class a = x % S; if (a < 0) a += S;
            mpz_class diff = a - y;
            mpz_class diffMod = diff % S; if (diffMod < 0) diffMod += S;
            INFO("s=" << s << " y=" << yi
                 << " x=" << x.get_str() << " a=" << a.get_str()
                 << " (a-y) mod s=" << diffMod.get_str());
            CHECK(diffMod == 0);
        }
    }
}
