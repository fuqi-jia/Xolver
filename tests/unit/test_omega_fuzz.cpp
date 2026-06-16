// Soundness fuzz for the Omega test: thousands of random small linear-integer
// systems, cross-checked against z3. The non-negotiable invariant is
//   Omega-Unsat  ⟹  z3-unsat        (a single violation = an unsound false UNSAT).
// It also reports COMPLETENESS (of the z3-unsat systems, how many Omega catches) —
// informative, not asserted (v1 is incomplete until the dark shadow lands).
//
// Skips gracefully if z3 is not on PATH (keeps CI green without z3).
#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/OmegaTest.h"

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

}  // namespace

TEST_CASE("omega: soundness fuzz vs z3 (Omega-Unsat => z3-unsat)") {
    // Gated: spawns ~1500 z3 processes (~30s), so off by default — run explicitly
    // with XOLVER_OMEGA_FUZZ=1 (the soundness gate before trusting the engine).
    if (!std::getenv("XOLVER_OMEGA_FUZZ")) { MESSAGE("set XOLVER_OMEGA_FUZZ=1 to run"); return; }
    if (!z3Available()) { MESSAGE("z3 not on PATH — skipping omega fuzz"); return; }

    std::mt19937 rng(0xC0FFEE);
    auto rnd = [&](int lo, int hi) { return lo + (int)(rng() % (unsigned)(hi - lo + 1)); };

    const int ITERS = 1500;
    int falseUnsat = 0, omegaUnsat = 0, z3Unsat = 0, caught = 0;

    for (int it = 0; it < ITERS; ++it) {
        const int nv = rnd(2, 4);
        const int nc = rnd(2, 6);
        std::vector<Constraint> cs;
        for (int j = 0; j < nc; ++j) {
            Constraint c;
            for (int v = 0; v < nv; ++v) {
                int a = rnd(-3, 3);
                if (a != 0) c.coeffs[v] = a;
            }
            if (c.coeffs.empty()) c.coeffs[rnd(0, nv - 1)] = rnd(1, 3);  // avoid trivial
            c.constant = rnd(-6, 6);
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
                MESSAGE("FALSE UNSAT: " << dump);
            }
        }
    }

    MESSAGE("omega fuzz: iters=" << ITERS << " omegaUnsat=" << omegaUnsat
            << " z3Unsat=" << z3Unsat << " caught=" << caught
            << " (completeness " << (z3Unsat ? 100 * caught / z3Unsat : 0) << "%)");
    CHECK(falseUnsat == 0);   // the soundness invariant
}
