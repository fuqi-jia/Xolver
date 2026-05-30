#include <doctest/doctest.h>
#include "theory/arith/poly/PolynomialKernel.h"
#include <functional>
#include <gmpxx.h>
#include <unordered_map>
#include <vector>

using namespace xolver;

namespace {

PolyId v(PolynomialKernel& k, const char* n) { return k.mkVar(k.getOrCreateVar(n)); }
PolyId c(PolynomialKernel& k, long x) { return k.mkConst(mpq_class(x)); }

// Evaluate `p` at the given integer assignment (uses kernel.evalInteger).
mpz_class evalIntAt(PolynomialKernel& k, PolyId p,
                    const std::unordered_map<std::string, mpz_class>& env) {
    auto v = k.evalInteger(p, env);
    REQUIRE(v.has_value());
    return *v;
}

// Soundness oracle: extractSymbolicResidue MUST return a polynomial that
// agrees with `(original mod modulus)` under EVERY non-zero integer
// assignment to the modulus variable, over a small {sample × extra-var}
// grid. This is the z3-style sanity check master asked for.
//
// We grid sample the modulus variable in {2..7} and any extra free vars
// (used by `original`) in {-3..3} (small but signed). For each grid point,
// (a) substitute and compute the integer value of `original` and `residue`,
// (b) check `original mod m == residue mod m` for the substituted m.
void checkResidueAgreesNumerically(PolynomialKernel& k,
                                   PolyId original, PolyId residue,
                                   PolyId modulus, const std::string& modulusVar,
                                   const std::vector<std::string>& extraVars) {
    auto modAtSample = [&](const std::unordered_map<std::string, mpz_class>& env) {
        return evalIntAt(k, modulus, env);
    };
    // Recursive grid walker over extraVars.
    std::unordered_map<std::string, mpz_class> env;
    int s_lo = 2, s_hi = 7;
    int x_lo = -3, x_hi = 3;
    std::function<void(size_t)> walk = [&](size_t i) {
        if (i == extraVars.size()) {
            for (int s = s_lo; s <= s_hi; ++s) {
                env[modulusVar] = mpz_class(s);
                mpz_class m = modAtSample(env);
                if (m == 0) continue;  // degenerate; modulus is symbolic
                mpz_class vo = evalIntAt(k, original, env);
                mpz_class vr = evalIntAt(k, residue, env);
                mpz_class a = vo % m; if (a < 0) a += (m > 0 ? m : -m);
                mpz_class b = vr % m; if (b < 0) b += (m > 0 ? m : -m);
                INFO("modulusVar=" << modulusVar << "=" << s
                     << " original=" << vo.get_str() << " residue=" << vr.get_str()
                     << " m=" << m.get_str() << " a=" << a.get_str() << " b=" << b.get_str());
                CHECK(a == b);
            }
            return;
        }
        for (int x = x_lo; x <= x_hi; ++x) {
            env[extraVars[i]] = mpz_class(x);
            walk(i + 1);
        }
    };
    walk(0);
}

} // namespace

// modInvStep family: (1 - k^2 * s^2) mod s^2 should reduce to 1.
TEST_CASE("extractSymbolicResidue: (1 - k^2 * s^2) mod s^2 == 1 (z3-validated)") {
    auto k = createPolynomialKernel();
    if (!k) return;  // libpoly unavailable

    PolyId s = v(*k, "s");
    PolyId kk = v(*k, "k");
    PolyId s2 = k->mul(s, s);
    PolyId k2 = k->mul(kk, kk);
    // poly = 1 - k^2 * s^2
    PolyId k2s2 = k->mul(k2, s2);
    PolyId one = c(*k, 1);
    PolyId poly = k->sub(one, k2s2);

    auto rOpt = k->extractSymbolicResidue(poly, s2);
    REQUIRE(rOpt.has_value());
    PolyId r = *rOpt;
    // The residue should be the constant 1.
    REQUIRE(k->isConstant(r));
    CHECK(k->toConstant(r) == mpq_class(1));

    // Cross-check the polynomial residue is numerically equivalent.
    checkResidueAgreesNumerically(*k, poly, r, s2, "s", {"k"});
}

TEST_CASE("extractSymbolicResidue: (s) mod s^2 = s  (degree < modulus passes through)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    PolyId s2 = k->mul(s, s);
    auto r = k->extractSymbolicResidue(s, s2);
    REQUIRE(r.has_value());
    CHECK(k->eq(*r, s));
    checkResidueAgreesNumerically(*k, s, *r, s2, "s", {});
}

TEST_CASE("extractSymbolicResidue: (s^2) mod s^2 = 0") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    PolyId s2 = k->mul(s, s);
    auto r = k->extractSymbolicResidue(s2, s2);
    REQUIRE(r.has_value());
    CHECK(k->isZero(*r));
}

TEST_CASE("extractSymbolicResidue: 0 mod s^2 = 0") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    PolyId s2 = k->mul(s, s);
    auto r = k->extractSymbolicResidue(k->mkZero(), s2);
    REQUIRE(r.has_value());
    CHECK(k->isZero(*r));
}

TEST_CASE("extractSymbolicResidue: (a + b*s + c*s^2) mod s^2 = a + b*s") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    PolyId a = v(*k, "a");
    PolyId b = v(*k, "b");
    PolyId c2 = v(*k, "c");
    PolyId s2 = k->mul(s, s);
    PolyId poly = k->add(a, k->add(k->mul(b, s), k->mul(c2, s2)));
    auto r = k->extractSymbolicResidue(poly, s2);
    REQUIRE(r.has_value());
    // Expected: a + b*s
    PolyId expected = k->add(a, k->mul(b, s));
    CHECK(k->eq(*r, expected));
    checkResidueAgreesNumerically(*k, poly, *r, s2, "s", {"a", "b", "c"});
}

// Fail-closed corner cases — Phase 1 returns nullopt and caller falls
// through. These tests pin the conservative behaviour: no wrong answer.

TEST_CASE("extractSymbolicResidue: constant modulus is rejected (Phase 1)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    PolyId r = k->extractSymbolicResidue(s, c(*k, 4)).value_or(NullPoly);
    CHECK(r == NullPoly);
}

TEST_CASE("extractSymbolicResidue: multi-variable modulus is rejected (Phase 1)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s"); PolyId t = v(*k, "t");
    auto r = k->extractSymbolicResidue(s, k->mul(s, t));
    CHECK_FALSE(r.has_value());
}

TEST_CASE("extractSymbolicResidue: non-monic modulus is rejected (Phase 1)") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId s = v(*k, "s");
    auto r = k->extractSymbolicResidue(s, k->mul(c(*k, 2), s));
    CHECK_FALSE(r.has_value());
}
