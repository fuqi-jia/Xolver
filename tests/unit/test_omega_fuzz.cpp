// Soundness + completeness fuzz for the Omega test: thousands of random small
// linear-integer systems, cross-checked against z3. Two invariants:
//   (1) SOUNDNESS  Omega-Unsat ⟹ z3-unsat   (one violation = an unsound false UNSAT).
//   (2) COMPLETENESS  z3-unsat ⟹ Omega-Unsat (within the node budget) — now that the
//       dark shadow + exact splinters (Pugh §2.3) make the engine integer-complete.
// Soundness is the release blocker; completeness is asserted on the small regime
// (budget never bites) and reported on the heavy regime (where it theoretically can).
//
// Skips gracefully if z3 is not on PATH (keeps CI green without z3).
#include <doctest/doctest.h>
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <string>
#include <unistd.h>

using namespace xolver::omega;

namespace {

bool z3Available() {
    return std::system("command -v z3 >/dev/null 2>&1") == 0;
}

std::string smtInt(const mpz_class& a) {
    return a < 0 ? ("(- " + mpz_class(-a).get_str() + ")") : a.get_str();
}

// Build an SMT-LIB QF_LIA assertion for the SAME constraint the engine sees.
std::string smtConstraint(const Constraint& c) {
    std::string sum;
    int terms = 0;
    std::string body;
    for (const auto& [v, a] : c.coeffs) {
        body += " (* " + smtInt(a) + " x" + std::to_string(v) + ")";
        ++terms;
    }
    body += " " + smtInt(c.constant);
    ++terms;
    sum = terms > 1 ? "(+" + body + ")" : body;
    const char* op = c.rel == Constraint::Eq ? "=" : c.rel == Constraint::Geq ? ">=" : "<=";
    return "(assert (" + std::string(op) + " " + sum + " 0))";
}

// Run z3 on a system; returns "sat" / "unsat" / "unknown".
std::string z3Verdict(int nv, const std::vector<Constraint>& cs) {
    std::string smt = "(set-logic QF_LIA)\n";
    for (int v = 0; v < nv; ++v) smt += "(declare-fun x" + std::to_string(v) + " () Int)\n";
    for (const auto& c : cs) smt += smtConstraint(c) + "\n";
    smt += "(check-sat)\n";

    char tmpl[] = "/tmp/omega_fuzz_XXXXXX";
    int fd = mkstemp(tmpl);
    if (fd < 0) return "error";
    { std::ofstream f(tmpl); f << smt; }
    close(fd);
    std::string cmd = "z3 -smt2 " + std::string(tmpl) + " 2>/dev/null";
    std::string out;
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

// One fuzz regime: `iters` random systems with the given size/coefficient ranges
// and seed. Reports {falseUnsat, z3Unsat, caught} via the out-params.
void runRegime(const char* name, unsigned seed, int iters, int vlo, int vhi,
               int clo, int chi, int coefMag, int constMag,
               int& falseUnsat, int& z3Unsat, int& caught) {
    std::mt19937 rng(seed);
    auto rnd = [&](int lo, int hi) { return lo + (int)(rng() % (unsigned)(hi - lo + 1)); };
    int omegaUnsat = 0;
    falseUnsat = z3Unsat = caught = 0;

    for (int it = 0; it < iters; ++it) {
        const int nv = rnd(vlo, vhi);
        const int nc = rnd(clo, chi);
        std::vector<Constraint> cs;
        for (int j = 0; j < nc; ++j) {
            Constraint c;
            for (int v = 0; v < nv; ++v) {
                int a = rnd(-coefMag, coefMag);
                if (a != 0) c.coeffs[v] = a;
            }
            if (c.coeffs.empty()) c.coeffs[rnd(0, nv - 1)] = rnd(1, coefMag);  // avoid trivial
            c.constant = rnd(-constMag, constMag);
            int r = rnd(0, 2);
            c.rel = r == 0 ? Constraint::Eq : r == 1 ? Constraint::Geq : Constraint::Leq;
            cs.push_back(std::move(c));
        }

        Result omega = decide(cs);              // decide() takes a copy
        std::string z3 = z3Verdict(nv, cs);
        if (z3 == "error" || z3 == "unknown") continue;

        if (omega == Result::Unsat) ++omegaUnsat;
        if (z3 == "unsat") ++z3Unsat;
        if (omega == Result::Unsat && z3 == "unsat") ++caught;

        if (omega == Result::Unsat && z3 == "sat") {     // ← UNSOUND
            ++falseUnsat;
            if (falseUnsat <= 3) {
                std::string dump;
                for (const auto& c : cs) dump += smtConstraint(c) + " ";
                MESSAGE("[" << name << "] FALSE UNSAT: " << dump);
            }
        }
        if (z3 == "unsat" && omega != Result::Unsat) {   // incompleteness (sound, but missed)
            static int missedShown = 0;
            if (missedShown++ < 6) {
                std::string dump;
                for (const auto& c : cs) dump += smtConstraint(c) + " ";
                MESSAGE("[" << name << "] MISSED (z3-unsat, omega no-claim): nv=" << nv << " : " << dump);
            }
        }
    }
    MESSAGE("omega fuzz [" << name << "]: iters=" << iters << " omegaUnsat=" << omegaUnsat
            << " z3Unsat=" << z3Unsat << " caught=" << caught
            << " (completeness " << (z3Unsat ? 100 * caught / z3Unsat : 0) << "%)");
}

}  // namespace

TEST_CASE("omega: soundness + completeness fuzz vs z3") {
    // Gated: spawns thousands of z3 processes (~1min), so off by default — run
    // explicitly with XOLVER_OMEGA_FUZZ=1 (the gate before trusting the engine).
    if (!std::getenv("XOLVER_OMEGA_FUZZ")) { MESSAGE("set XOLVER_OMEGA_FUZZ=1 to run"); return; }
    if (!z3Available()) { MESSAGE("z3 not on PATH — skipping omega fuzz"); return; }

    int fu, z3u, caught;

    // Small regime: coeffs/consts well within the node budget ⇒ the engine is
    // integer-complete here, so BOTH invariants are hard-asserted.
    runRegime("small", 0xC0FFEE, 1500, 2, 4, 2, 6, 3, 6, fu, z3u, caught);
    CHECK(fu == 0);            // SOUNDNESS — release blocker
    CHECK(caught == z3u);      // COMPLETENESS — every z3-unsat caught (dark shadow + splinters)

    // Heavy regime: bigger coeffs ⇒ more both-coefficient>1 pairs ⇒ exercises the
    // dark-shadow gap + splinter recursion much harder. Different seed. Soundness is
    // still hard-asserted; completeness is reported (the budget can in principle bite).
    runRegime("heavy", 0x5EED1234, 2000, 2, 5, 3, 8, 5, 12, fu, z3u, caught);
    CHECK(fu == 0);            // SOUNDNESS — release blocker
    CHECK(caught >= z3u * 99 / 100);   // completeness should stay ~100% even here
}
