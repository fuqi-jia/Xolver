#include <doctest/doctest.h>
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"

using namespace xolver::omega;

namespace {
Constraint eq(std::map<int, mpz_class> c, long k) {
    Constraint x; x.coeffs = std::move(c); x.constant = k; x.rel = Constraint::Eq; return x;
}
Constraint geq(std::map<int, mpz_class> c, long k) {
    Constraint x; x.coeffs = std::move(c); x.constant = k; x.rel = Constraint::Geq; return x;
}
Constraint leq(std::map<int, mpz_class> c, long k) {
    Constraint x; x.coeffs = std::move(c); x.constant = k; x.rel = Constraint::Leq; return x;
}
}  // namespace

// ───────────────────────── Stage 0: normalize + gcd ─────────────────────────

TEST_CASE("omega: gcd ∤ const equality is UNSAT") {
    // 2x - 1 = 0  → gcd(2)=2 ∤ 1 → no integer x
    CHECK(decide({eq({{0, 2}}, -1)}) == Result::Unsat);
    // 6x + 4y + 1 = 0 → gcd(6,4)=2 ∤ 1
    CHECK(decide({eq({{0, 6}, {1, 4}}, 1)}) == Result::Unsat);
}

TEST_CASE("omega: solvable equality is NOT claimed unsat") {
    CHECK(decide({eq({{0, 2}}, -4)}) == Result::SatOrUnknown);   // 2x=4 → x=2
    CHECK(decide({eq({{0, 6}, {1, 4}}, 2)}) == Result::SatOrUnknown);  // gcd 2 | 2
}

TEST_CASE("omega: pure-constant contradictions") {
    CHECK(decide({geq({}, -1)}) == Result::Unsat);     // -1 >= 0
    CHECK(decide({eq({}, 3)}) == Result::Unsat);        //  3 == 0
    CHECK(decide({geq({}, 5)}) == Result::SatOrUnknown);// 5 >= 0 (fine)
    CHECK(decide({eq({}, 0)}) == Result::SatOrUnknown); // 0 == 0 (fine)
}

TEST_CASE("omega: Leq is normalized to Geq (no spurious verdict)") {
    // x <= 2  i.e. (x - 2) <= 0  → (-x + 2) >= 0 ; satisfiable
    CHECK(decide({leq({{0, 1}}, -2)}) == Result::SatOrUnknown);
    // 2 <= 0  → constant-only contradiction
    CHECK(decide({leq({}, 2)}) == Result::Unsat);
}

// ───────────────────── Stage 1: equality elimination ─────────────────────

TEST_CASE("omega: over-determined equalities (±1 pivot) UNSAT") {
    // x = 0  ∧  x = 1
    CHECK(decide({eq({{0, 1}}, 0), eq({{0, 1}}, -1)}) == Result::Unsat);
    // x + y = 0 ∧ x + y = 1
    CHECK(decide({eq({{0, 1}, {1, 1}}, 0), eq({{0, 1}, {1, 1}}, -1)}) == Result::Unsat);
}

TEST_CASE("omega: solvable equality needing balanced-residue reduction") {
    // 2x + 3y = 1 (no ±1 coeff, gcd=1) → solvable (x=-1,y=1) → no false UNSAT
    CHECK(decide({eq({{0, 2}, {1, 3}}, -1)}) == Result::SatOrUnknown);
    // 6x + 10y + 15z = 1 (gcd=1, no ±1) → solvable
    CHECK(decide({eq({{0, 6}, {1, 10}, {2, 15}}, -1)}) == Result::SatOrUnknown);
}

TEST_CASE("omega: contradiction surfaced AFTER reduction") {
    // 2x + 3y = 0 ∧ 2x + 3y = 1 — same form, different RHS → 0 = 1
    CHECK(decide({eq({{0, 2}, {1, 3}}, 0), eq({{0, 2}, {1, 3}}, -1)}) == Result::Unsat);
    // 4x + 6y = 2 ∧ 6x + 9y = 2 : (1)→2x+3y=1, (2) gcd(6,9)=3∤2 → UNSAT (normalize)
    CHECK(decide({eq({{0, 4}, {1, 6}}, -2), eq({{0, 6}, {1, 9}}, -2)}) == Result::Unsat);
}

TEST_CASE("omega: equality + inequalities, no false UNSAT") {
    // x = 5 ∧ x >= 0 ∧ x <= 10 → SAT; must NOT be claimed UNSAT
    CHECK(decide({eq({{0, 1}}, -5), geq({{0, 1}}, 0), leq({{0, 1}}, -10)})
          == Result::SatOrUnknown);
}

// ───────────────────── Stage 2: real-shadow FM ─────────────────────

TEST_CASE("omega: 1-var bound contradiction") {
    // x >= 1 ∧ x <= 0
    CHECK(decide({geq({{0, 1}}, -1), leq({{0, 1}}, 0)}) == Result::Unsat);
}

TEST_CASE("omega: 2-var FM contradiction") {
    // x + y >= 1 ∧ x + y <= 0
    CHECK(decide({geq({{0, 1}, {1, 1}}, -1), leq({{0, 1}, {1, 1}}, 0)}) == Result::Unsat);
    // x >= y+1 ∧ y >= x+1   (x-y-1>=0 ∧ y-x-1>=0 → -2>=0)
    CHECK(decide({geq({{0, 1}, {1, -1}}, -1), geq({{0, -1}, {1, 1}}, -1)}) == Result::Unsat);
}

TEST_CASE("omega: integer tightening catches 2x in [1,1]") {
    // 2x >= 1 ∧ 2x <= 1 → no integer (2x=1); tightening → x>=1 ∧ x<=0 → UNSAT
    CHECK(decide({geq({{0, 2}}, -1), leq({{0, 2}}, -1)}) == Result::Unsat);
}

TEST_CASE("omega: satisfiable inequality systems are NOT claimed unsat") {
    // 0 <= x <= 10 ∧ 0 <= y <= 10 ∧ x + y >= 5
    CHECK(decide({geq({{0, 1}}, 0), leq({{0, 1}}, -10),
                  geq({{1, 1}}, 0), leq({{1, 1}}, -10),
                  geq({{0, 1}, {1, 1}}, -5)}) == Result::SatOrUnknown);
    // triangle x>=0, y>=0, x+y<=4  → SAT
    CHECK(decide({geq({{0, 1}}, 0), geq({{1, 1}}, 0), leq({{0, 1}, {1, 1}}, -4)})
          == Result::SatOrUnknown);
}

// ───────────── Stage 3: DARK shadow + exact splinters (T6) ─────────────
// These are the integer-specific cases: the REAL relaxation is feasible, yet no
// integer point exists. The pre-T6 real-shadow-only engine returned SatOrUnknown
// here; the dark shadow + splinter recursion proves them UNSAT. (All z3-confirmed.)

TEST_CASE("omega: dark shadow — box 2x+3y=4 in [0,1]^2 is integer-infeasible") {
    // Real point x=0.5,y=1 satisfies 2x+3y=4; no integer (x,y)∈{0,1}² hits 4.
    std::vector<Constraint> box = {
        geq({{0, 2}, {1, 3}}, -4), leq({{0, 2}, {1, 3}}, -4),   // 2x+3y = 4
        geq({{0, 1}}, 0), leq({{0, 1}}, -1),                    // 0 <= x <= 1
        geq({{1, 1}}, 0), leq({{1, 1}}, -1),                    // 0 <= y <= 1
    };
    CHECK(decide(box) == Result::Unsat);
    // Same region stated as a single equality — equality elimination then bounds.
    CHECK(decide({eq({{0, 2}, {1, 3}}, -4),
                  geq({{0, 1}}, 0), leq({{0, 1}}, -1),
                  geq({{1, 1}}, 0), leq({{1, 1}}, -1)}) == Result::Unsat);
}

TEST_CASE("omega: dark shadow — thin slab 2x<=3y<=2x+1 pinned at x=2") {
    // 3y ∈ [2x, 2x+1]; at x=2 the window is [4,5] with no multiple of 3 → the dark
    // shadow fails AND both splinters (3y=4, 3y=5) are empty ⇒ UNSAT.
    std::vector<Constraint> s = {
        geq({{0, -2}, {1, 3}}, 0),    // 3y - 2x >= 0
        leq({{0, -2}, {1, 3}}, -1),   // 3y - 2x <= 1
        geq({{0, 1}}, -2), leq({{0, 1}}, -2),   // x = 2
    };
    CHECK(decide(s) == Result::Unsat);
}

TEST_CASE("omega: splinter SAT control — dark fails but a splinter succeeds") {
    // 3y ∈ [2x, 2x+1] with 0<=x<=1. The dark shadow fails (window < 1), but x=0 ⇒
    // 3y∈[0,1] ⇒ y=0 works. The splinter recursion MUST find it and NOT claim UNSAT.
    std::vector<Constraint> s = {
        geq({{0, -2}, {1, 3}}, 0),    // 3y - 2x >= 0
        leq({{0, -2}, {1, 3}}, -1),   // 3y - 2x <= 1
        geq({{0, 1}}, 0), leq({{0, 1}}, -1),     // 0 <= x <= 1
    };
    CHECK(decide(s) == Result::SatOrUnknown);   // over-claiming here would be UNSOUND
}

TEST_CASE("omega: dark shadow — three-variable integer-infeasible band") {
    // 2x+3y+5z = 1 has integer solutions, but constrained to z=0 and 0<=x,y<=1 the
    // residual 2x+3y=1 over the unit box is empty (z3-confirmed unsat).
    std::vector<Constraint> s = {
        eq({{0, 2}, {1, 3}, {2, 5}}, -1),       // 2x+3y+5z = 1
        geq({{2, 1}}, 0), leq({{2, 1}}, 0),     // z = 0
        geq({{0, 1}}, 0), leq({{0, 1}}, -1),    // 0 <= x <= 1
        geq({{1, 1}}, 0), leq({{1, 1}}, -1),    // 0 <= y <= 1
    };
    CHECK(decide(s) == Result::Unsat);
}
