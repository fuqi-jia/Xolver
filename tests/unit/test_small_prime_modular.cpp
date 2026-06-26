// SmallPrimeModular: GF(p) consistency of the equality subsystem over a small-prime
// schedule. The reasoner only ever asserts Unsat, so the soundness invariant is
//   modular-Unsat ⟹ the integer system is genuinely infeasible.
// Crafted cases check the system-level obstructions a per-equation gcd test misses;
// the gated z3 fuzz (XOLVER_MODULAR_FUZZ=1) is the soundness gate.
#include <doctest/doctest.h>
#include "theory/arith/logics/nia/reasoners/SmallPrimeModular.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <string>
#include <unistd.h>

using namespace xolver;

namespace {
omega::Constraint eq(std::map<int, mpz_class> c, long k) {
    omega::Constraint x;
    x.coeffs = std::move(c);
    x.constant = k;
    x.rel = omega::Constraint::Eq;
    return x;
}
omega::Constraint geq(std::map<int, mpz_class> c, long k) {
    omega::Constraint x;
    x.coeffs = std::move(c);
    x.constant = k;
    x.rel = omega::Constraint::Geq;
    return x;
}
}  // namespace

TEST_CASE("modular: derived 2x=1 obstruction (mod 2) the per-eq gcd misses") {
    // x + y = 0 ∧ x − y = 1  ⟹  2x = 1, infeasible. Each equation alone has
    // coefficient-gcd 1, so the per-equation gcd test cannot see it; mod 2 does.
    CHECK(modular::decide({eq({{0, 1}, {1, 1}}, 0), eq({{0, 1}, {1, -1}}, -1)})
          == modular::Result::Unsat);
}

TEST_CASE("modular: system inconsistent mod 3 only") {
    // 3x + y = 1 ∧ y = 0  ⟹  3x = 1, infeasible. Consistent mod 2 (x+y=1,y=0 ⇒ x=1),
    // inconsistent mod 3 (3≡0 ⇒ y≡1 contradicts y=0). Schedule must reach p=3.
    CHECK(modular::decide({eq({{0, 3}, {1, 1}}, -1), eq({{1, 1}}, 0)})
          == modular::Result::Unsat);
}

TEST_CASE("modular: single-equation gcd obstruction still caught") {
    // 2x = 1  → infeasible mod 2.
    CHECK(modular::decide({eq({{0, 2}}, -1)}) == modular::Result::Unsat);
    // 6x + 4y = 1 → gcd 2 ∤ 1; infeasible mod 2.
    CHECK(modular::decide({eq({{0, 6}, {1, 4}}, -1)}) == modular::Result::Unsat);
}

TEST_CASE("modular: feasible systems are NOT claimed unsat") {
    // x + y = 0 ∧ x − y = 2  ⟹  x=1, y=−1 (integer).
    CHECK(modular::decide({eq({{0, 1}, {1, 1}}, 0), eq({{0, 1}, {1, -1}}, -2)})
          == modular::Result::SatOrUnknown);
    // 2x + 3y = 1 (gcd 1, solvable: x=−1,y=1).
    CHECK(modular::decide({eq({{0, 2}, {1, 3}}, -1)}) == modular::Result::SatOrUnknown);
    // pure constants / empty.
    CHECK(modular::decide({}) == modular::Result::SatOrUnknown);
}

TEST_CASE("modular: inequalities are ignored (no claim from a bound alone)") {
    // Only inequalities → no equality rows → SatOrUnknown (even if jointly unsat,
    // modular reasoning over the empty equality subset makes no claim).
    CHECK(modular::decide({geq({{0, 1}}, -1), geq({{0, -1}}, -1)})
          == modular::Result::SatOrUnknown);
    // A mix: the equality 2x=1 is still caught despite the extra inequality.
    CHECK(modular::decide({geq({{0, 1}}, 0), eq({{0, 2}}, -1)})
          == modular::Result::Unsat);
}

// ───────────────────────── soundness fuzz vs z3 ─────────────────────────

namespace {
bool z3Available() { return std::system("command -v z3 >/dev/null 2>&1") == 0; }

std::string smtInt(const mpz_class& a) {
    return a < 0 ? ("(- " + mpz_class(-a).get_str() + ")") : a.get_str();
}
std::string z3Verdict(int nv, const std::vector<omega::Constraint>& cs) {
    std::string smt = "(set-logic QF_LIA)\n";
    for (int v = 0; v < nv; ++v) smt += "(declare-fun x" + std::to_string(v) + " () Int)\n";
    for (const auto& c : cs) {
        std::string body;
        for (const auto& [v, a] : c.coeffs)
            body += " (* " + smtInt(a) + " x" + std::to_string(v) + ")";
        body += " " + smtInt(c.constant);
        smt += "(assert (= (+" + body + ") 0))\n";   // fuzz uses equalities only
    }
    smt += "(check-sat)\n";
    char tmpl[] = "/tmp/modular_fuzz_XXXXXX";
    int fd = mkstemp(tmpl);
    if (fd < 0) return "error";
    { std::ofstream f(tmpl); f << smt; }
    close(fd);
    std::string out, cmd = "z3 -smt2 " + std::string(tmpl) + " 2>/dev/null";
    if (FILE* p = popen(cmd.c_str(), "r")) {
        char buf[256];
        while (fgets(buf, sizeof(buf), p)) out += buf;
        pclose(p);
    }
    std::remove(tmpl);
    if (out.find("unsat") != std::string::npos) return "unsat";
    if (out.find("sat") != std::string::npos) return "sat";
    return "unknown";
}
}  // namespace

TEST_CASE("modular: soundness fuzz vs z3 (modular-Unsat => z3-unsat)") {
    if (!std::getenv("XOLVER_MODULAR_FUZZ")) { MESSAGE("set XOLVER_MODULAR_FUZZ=1 to run"); return; }
    if (!z3Available()) { MESSAGE("z3 not on PATH — skipping modular fuzz"); return; }

    std::mt19937 rng(0xA11CE);
    auto rnd = [&](int lo, int hi) { return lo + (int)(rng() % (unsigned)(hi - lo + 1)); };

    const int ITERS = 2000;
    int falseUnsat = 0, modUnsat = 0, z3Unsat = 0, caught = 0;
    for (int it = 0; it < ITERS; ++it) {
        const int nv = rnd(2, 4);
        const int nc = rnd(2, 5);
        std::vector<omega::Constraint> cs;
        for (int j = 0; j < nc; ++j) {
            std::map<int, mpz_class> m;
            for (int v = 0; v < nv; ++v) { int a = rnd(-4, 4); if (a) m[v] = a; }
            if (m.empty()) m[rnd(0, nv - 1)] = rnd(1, 4);
            cs.push_back(eq(std::move(m), rnd(-8, 8)));
        }
        auto r = modular::decide(cs);
        std::string z3 = z3Verdict(nv, cs);
        if (z3 == "error" || z3 == "unknown") continue;
        if (r == modular::Result::Unsat) ++modUnsat;
        if (z3 == "unsat") ++z3Unsat;
        if (r == modular::Result::Unsat && z3 == "unsat") ++caught;
        if (r == modular::Result::Unsat && z3 == "sat") ++falseUnsat;   // ← UNSOUND
    }
    MESSAGE("modular fuzz: iters=" << ITERS << " modUnsat=" << modUnsat
            << " z3Unsat=" << z3Unsat << " caught=" << caught
            << " (of-z3-unsat " << (z3Unsat ? 100 * caught / z3Unsat : 0) << "%)");
    CHECK(falseUnsat == 0);   // the soundness invariant
}
