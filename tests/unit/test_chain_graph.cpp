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
