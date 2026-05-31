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

// ---------------------------------------------------------------------------
// Gomory Mixed-Integer (GMI) cut — deriveGmiCut. Same soundness contract: the
// cut Σ psi_j y_j >= f0 must be violated at y=0 and valid for every feasible
// point. Now SOME y_j may be continuous (range over a rational grid); only
// points where x_i is integral are feasible and must be preserved.
// ---------------------------------------------------------------------------
namespace {

// Brute force over a rational grid. Integer terms step by 1; continuous terms
// step by 1/D. A point is feasible iff x_i = beta + Σ chat_j y_j is integral;
// every feasible point must satisfy Σ psi_j y_j >= rhs.
bool gmiCutIsValid(const mpq_class& beta, const std::vector<mpq_class>& chat,
                   const std::vector<bool>& isInt,
                   const std::vector<mpq_class>& psi, const mpq_class& rhs,
                   int K, int D) {
    int n = static_cast<int>(chat.size());
    std::vector<int> step(n, 0);                  // y_j = step_j * unit_j
    std::vector<int> maxStep(n);
    std::vector<mpq_class> unit(n);
    for (int j = 0; j < n; ++j) {
        unit[j] = isInt[j] ? mpq_class(1) : mpq_class(1, D);
        maxStep[j] = isInt[j] ? K : K * D;
    }
    while (true) {
        mpq_class xi = beta;
        std::vector<mpq_class> y(n);
        for (int j = 0; j < n; ++j) { y[j] = unit[j] * mpq_class(step[j]); xi += chat[j] * y[j]; }
        if (isIntegral(xi)) {
            mpq_class lhs(0);
            for (int j = 0; j < n; ++j) lhs += psi[j] * y[j];
            if (lhs < rhs) return false;          // feasible point cut off -> UNSOUND
        }
        int p = 0;
        for (; p < n; ++p) { if (++step[p] <= maxStep[p]) break; step[p] = 0; }
        if (p == n) break;
    }
    return true;
}

void checkGmiRow(const mpq_class& beta, const std::vector<mpq_class>& chat,
                 const std::vector<bool>& isInt) {
    mpq_class f0 = gmiFractionalPart(beta);
    REQUIRE(f0 > 0);
    REQUIRE(f0 < 1);
    std::vector<GmiNonbasicTerm> terms;
    for (size_t j = 0; j < chat.size(); ++j) terms.push_back({chat[j], isInt[j]});
    auto cut = deriveGmiCut(f0, terms);
    REQUIRE(cut.has_value());
    for (const auto& g : cut->gamma) CHECK(g >= 0);     // (a) violated at y=0
    CHECK(cut->rhs == f0);
    CHECK(cut->rhs > 0);
    // (b) validity by brute force over the mixed grid.
    CHECK(gmiCutIsValid(beta, chat, isInt, cut->gamma, cut->rhs, /*K=*/4, /*D=*/4));
}

} // namespace

TEST_CASE("GMI cut: pure-integer rows match the soundness contract") {
    checkGmiRow(mpq_class(7, 3), {mpq_class(2, 3), mpq_class(-1, 3)}, {true, true});
    checkGmiRow(mpq_class(5, 4), {mpq_class(1, 4), mpq_class(3, 4), mpq_class(-1, 2)}, {true, true, true});
    checkGmiRow(mpq_class(11, 6), {mpq_class(5, 6), mpq_class(1, 6), mpq_class(1, 3)}, {true, true, true});
    checkGmiRow(mpq_class(8, 7), {mpq_class(3, 7), mpq_class(-2, 7), mpq_class(6, 7)}, {true, true, true});
}

TEST_CASE("GMI cut: mixed integer + continuous rows are sound (the pure cut bails here)") {
    // Each row has at least one continuous nonbasic, where deriveGomoryCut would
    // return nullopt; deriveGmiCut must produce a valid cut instead.
    checkGmiRow(mpq_class(3, 2), {mpq_class(1, 2), mpq_class(-1, 2)}, {true, false});
    checkGmiRow(mpq_class(7, 3), {mpq_class(2, 3), mpq_class(-1, 3)}, {false, true});
    checkGmiRow(mpq_class(5, 4), {mpq_class(3, 4), mpq_class(1, 2), mpq_class(-2, 3)}, {true, false, false});
    checkGmiRow(mpq_class(1, 3), {mpq_class(5, 6), mpq_class(-7, 6)}, {false, false});
    checkGmiRow(mpq_class(9, 5), {mpq_class(2, 5), mpq_class(-3, 5), mpq_class(1, 1)}, {true, false, true});
}

TEST_CASE("GMI cut: produces a cut on a continuous term where pure Gomory bails") {
    std::vector<GmiNonbasicTerm> terms{{mpq_class(1, 2), true}, {mpq_class(-1, 2), false}};
    CHECK(!deriveGomoryCut(mpq_class(1, 2), terms).has_value());   // pure: bails
    auto gmi = deriveGmiCut(mpq_class(1, 2), terms);               // GMI: succeeds
    REQUIRE(gmi.has_value());
    CHECK(gmi->rhs == mpq_class(1, 2));
    for (const auto& g : gmi->gamma) CHECK(g >= 0);
}

TEST_CASE("GMI cut: all-integer-coefficient row is vacuous -> nullopt") {
    std::vector<GmiNonbasicTerm> terms{{mpq_class(2), true}, {mpq_class(-3), true}};
    CHECK(!deriveGmiCut(mpq_class(1, 2), terms).has_value());
}

TEST_CASE("GMI cut: f0 out of (0,1) -> nullopt") {
    std::vector<GmiNonbasicTerm> terms{{mpq_class(1, 2), false}};
    CHECK(!deriveGmiCut(mpq_class(0), terms).has_value());
    CHECK(!deriveGmiCut(mpq_class(1), terms).has_value());
}
