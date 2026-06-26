// IntBoundProp: integer interval bound propagation over equality systems. It only
// ever TIGHTENS bounds / reports Unsat, so the soundness invariants are:
//   (1) Unsat ⟹ the system has no integer solution in the seed box.
//   (2) every integer solution in the seed box stays within the tightened bounds
//       (no over-tightening).
// The brute-force fuzz checks BOTH exhaustively over a small box (no z3 needed).
#include <doctest/doctest.h>
#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"

#include <cstdlib>
#include <functional>
#include <random>
#include <vector>

using namespace xolver;

namespace {
omega::Constraint eq(std::map<int, mpz_class> c, long k) {
    omega::Constraint x;
    x.coeffs = std::move(c);
    x.constant = k;
    x.rel = omega::Constraint::Eq;
    return x;
}
intprop::Bound box(long lo, long hi) {
    intprop::Bound b; b.hasLo = b.hasHi = true; b.lo = lo; b.hi = hi; return b;
}
}  // namespace

TEST_CASE("intprop: single-eq infeasibility 2x=1 ⇒ Unsat") {
    std::map<int, intprop::Bound> b{{0, box(-10, 10)}};
    CHECK(intprop::propagate({eq({{0, 2}}, -1)}, b) == intprop::Result::Unsat);
}

TEST_CASE("intprop: derived combination obstruction is NOT claimed (incomplete but sound)") {
    // x+y=0 ∧ x−y=1 force 2x=1 (integer-infeasible), but interval propagation never
    // FORMS the combination — it tightens per equation only. So it returns Ok here
    // (sound: no false Unsat). Catching the derived obstruction is the modular
    // reasoner's job ([[SmallPrimeModular]]); the two are complementary.
    std::map<int, intprop::Bound> b{{0, box(-10, 10)}, {1, box(-10, 10)}};
    CHECK(intprop::propagate({eq({{0, 1}, {1, 1}}, 0), eq({{0, 1}, {1, -1}}, -1)}, b)
          == intprop::Result::Ok);
}

TEST_CASE("intprop: x=2y with y∈[1,3] tightens x to [2,6]") {
    std::map<int, intprop::Bound> b{{0, box(-100, 100)}, {1, box(1, 3)}};
    REQUIRE(intprop::propagate({eq({{0, 1}, {1, -2}}, 0)}, b) == intprop::Result::Ok);
    CHECK(b[0].lo == 2);
    CHECK(b[0].hi == 6);
}

TEST_CASE("intprop: integer floor/ceil tighten 2x=y, y∈[1,4] ⇒ x∈[1,2]") {
    std::map<int, intprop::Bound> b{{0, box(-100, 100)}, {1, box(1, 4)}};
    REQUIRE(intprop::propagate({eq({{0, 2}, {1, -1}}, 0)}, b) == intprop::Result::Ok);
    CHECK(b[0].lo == 1);   // ceil(1/2)
    CHECK(b[0].hi == 2);   // floor(4/2)
}

TEST_CASE("intprop: feasible system is not over-tightened") {
    std::map<int, intprop::Bound> b{{0, box(0, 5)}, {1, box(0, 5)}};
    REQUIRE(intprop::propagate({eq({{0, 1}, {1, 1}}, -5)}, b) == intprop::Result::Ok);
    CHECK(b[0].lo == 0); CHECK(b[0].hi == 5);   // x = 5 − y, y∈[0,5] ⇒ x∈[0,5]
}

// ───────────────────── brute-force soundness fuzz ─────────────────────

namespace {
bool satisfiesAll(const std::vector<omega::Constraint>& cs, const std::vector<long>& x) {
    for (const auto& c : cs) {
        mpz_class s = c.constant;
        for (const auto& [v, a] : c.coeffs) s += a * x[v];
        if (s != 0) return false;
    }
    return true;
}
}  // namespace

TEST_CASE("intprop: brute-force soundness fuzz (no over-tightening, no false Unsat)") {
    std::mt19937 rng(0xB00DED);
    auto rnd = [&](int lo, int hi) { return lo + (int)(rng() % (unsigned)(hi - lo + 1)); };

    const int ITERS = 4000;
    const int LO = -4, HI = 4;
    int unsatClaims = 0, overTighten = 0, falseUnsat = 0;

    for (int it = 0; it < ITERS; ++it) {
        const int nv = rnd(2, 3);
        const int nc = rnd(1, 3);
        std::vector<omega::Constraint> cs;
        for (int j = 0; j < nc; ++j) {
            std::map<int, mpz_class> m;
            for (int v = 0; v < nv; ++v) { int a = rnd(-3, 3); if (a) m[v] = a; }
            if (m.empty()) m[rnd(0, nv - 1)] = rnd(1, 3);
            cs.push_back(eq(std::move(m), rnd(-5, 5)));
        }
        std::map<int, intprop::Bound> b;
        for (int v = 0; v < nv; ++v) b[v] = box(LO, HI);

        auto res = intprop::propagate(cs, b);

        // Brute-force every integer point in the seed box.
        std::vector<long> x(nv);
        bool anySol = false;
        bool outside = false;
        std::function<void(int)> rec = [&](int v) {
            if (v == nv) {
                if (!satisfiesAll(cs, x)) return;
                anySol = true;
                for (int k = 0; k < nv; ++k) {
                    const auto& bk = b[k];
                    if ((bk.hasLo && x[k] < bk.lo) || (bk.hasHi && x[k] > bk.hi)) outside = true;
                }
                return;
            }
            for (long val = LO; val <= HI; ++val) { x[v] = val; rec(v + 1); }
        };
        rec(0);

        if (res == intprop::Result::Unsat) { ++unsatClaims; if (anySol) ++falseUnsat; }
        else if (outside) ++overTighten;
    }

    MESSAGE("intprop fuzz: iters=" << ITERS << " unsatClaims=" << unsatClaims
            << " falseUnsat=" << falseUnsat << " overTighten=" << overTighten);
    CHECK(falseUnsat == 0);    // soundness: a claimed Unsat with a real solution = unsound
    CHECK(overTighten == 0);   // soundness: a real solution outside the tightened bounds = unsound
}
