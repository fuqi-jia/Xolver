// Soundness verification for the GMI cut derivation (XOLVER_LIA_CUTS core).
// For a row x_i = beta_i + Σ chat_j y_j (y_j >= 0 integer, x_i integer), the
// derived cut Σ gamma_j y_j >= 1 must (a) be violated at the current point
// y = 0, and (b) hold for EVERY integer-feasible point. (b) is checked by brute
// force over a bounded box — the "localized per-cut validity check".

#include <doctest/doctest.h>
#include "theory/arith/lia/GomoryCut.h"
#include <gmpxx.h>
#include <vector>

using namespace xolver;

namespace {

bool isIntegral(const mpq_class& q) { return q.get_den() == 1; }

// Brute-force: enumerate y in [0,K]^n; for every point where x_i is integral
// (feasible), require Σ gamma_j y_j >= rhs. Returns true if the cut removes no
// feasible integer point (sound).
bool cutIsValid(const mpq_class& beta, const std::vector<mpq_class>& chat,
                const std::vector<mpq_class>& gamma, const mpq_class& rhs, int K) {
    int n = static_cast<int>(chat.size());
    std::vector<int> y(n, 0);
    while (true) {
        // x_i = beta + Σ chat_j y_j
        mpq_class xi = beta;
        for (int j = 0; j < n; ++j) xi += chat[j] * mpq_class(y[j]);
        if (isIntegral(xi)) {
            mpq_class lhs(0);
            for (int j = 0; j < n; ++j) lhs += gamma[j] * mpq_class(y[j]);
            if (lhs < rhs) return false;  // feasible point cut off -> UNSOUND
        }
        // increment odometer
        int p = 0;
        for (; p < n; ++p) {
            if (++y[p] <= K) break;
            y[p] = 0;
        }
        if (p == n) break;
    }
    return true;
}

GomoryCutResult mustDerive(const mpq_class& f0, const std::vector<mpq_class>& chat) {
    std::vector<GmiNonbasicTerm> terms;
    for (const auto& c : chat) terms.push_back({c, /*isInteger=*/true});
    auto r = deriveGomoryCut(f0, terms);
    REQUIRE(r.has_value());
    return *r;
}

void checkRow(const mpq_class& beta, const std::vector<mpq_class>& chat) {
    mpq_class f0 = gmiFractionalPart(beta);
    REQUIRE(f0 > 0);
    REQUIRE(f0 < 1);
    auto cut = mustDerive(f0, chat);
    // (a) all gamma >= 0; rhs > 0 so the current point y=0 (LHS 0) is cut off.
    for (const auto& g : cut.gamma) CHECK(g >= 0);
    CHECK(cut.rhs > 0);
    // (b) validity by brute force: no integer-feasible point is removed.
    CHECK(cutIsValid(beta, chat, cut.gamma, cut.rhs, /*K=*/6));
}

} // namespace

TEST_CASE("GMI cut: fractionalPart basics") {
    CHECK(gmiFractionalPart(mpq_class(3, 2)) == mpq_class(1, 2));
    CHECK(gmiFractionalPart(mpq_class(-1, 3)) == mpq_class(2, 3));
    CHECK(gmiFractionalPart(mpq_class(2)) == 0);
}

TEST_CASE("GMI cut: worked example x = 3/2 + 1/2 y1 + 1/3 y2") {
    auto cut = mustDerive(mpq_class(1, 2), {mpq_class(1, 2), mpq_class(1, 3)});
    CHECK(cut.gamma[0] == mpq_class(1, 2));    // frac(1/2)
    CHECK(cut.gamma[1] == mpq_class(1, 3));    // frac(1/3)
    CHECK(cut.rhs == mpq_class(1, 2));         // 1 - f0
    checkRow(mpq_class(3, 2), {mpq_class(1, 2), mpq_class(1, 3)});
}

TEST_CASE("GMI cut: validity over many integer rows (brute force)") {
    // Mix of fractional betas and coefficients (positive, negative, >f0, <f0).
    checkRow(mpq_class(7, 3), {mpq_class(2, 3), mpq_class(-1, 3)});
    checkRow(mpq_class(5, 4), {mpq_class(1, 4), mpq_class(3, 4), mpq_class(-1, 2)});
    checkRow(mpq_class(1, 5), {mpq_class(2, 5), mpq_class(4, 5)});
    checkRow(mpq_class(11, 6), {mpq_class(5, 6), mpq_class(1, 6), mpq_class(1, 3)});
    checkRow(mpq_class(-3, 2), {mpq_class(1, 2), mpq_class(-3, 4)});
    checkRow(mpq_class(8, 7), {mpq_class(3, 7), mpq_class(-2, 7), mpq_class(6, 7)});
}

TEST_CASE("GMI cut: integer-coefficient nonbasic contributes zero (no spurious cut)") {
    // chat with integer value -> fractional part 0; if ALL are integral the cut
    // is vacuous (signals a different conflict) and derivation returns nullopt.
    std::vector<GmiNonbasicTerm> terms{{mpq_class(2), true}, {mpq_class(-3), true}};
    CHECK(!deriveGomoryCut(mpq_class(1, 2), terms).has_value());
}

TEST_CASE("GMI cut: any continuous (non-integer) term -> no cut (sound skip)") {
    std::vector<GmiNonbasicTerm> terms{{mpq_class(1, 2), true}, {mpq_class(-1, 2), false}};
    CHECK(!deriveGomoryCut(mpq_class(1, 2), terms).has_value());
}
