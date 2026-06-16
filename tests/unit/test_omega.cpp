#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/OmegaTest.h"

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
