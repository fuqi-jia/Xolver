// CAC engine (module C — get_unsat_cover). End-to-end: 1- and 2-variable SAT
// and UNSAT QF_NRA problems solved by conflict-driven coverings (no full
// closure). SAT status means the engine found a full sample validating every
// constraint (its leaf check); UNSAT means a gap-free covering.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include <algorithm>
#include <vector>
#include "theory/arith/nra/cac/CacEngine.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"
#endif

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

static RationalPolynomial K(long c) { return RationalPolynomial::fromConstant(mpq_class(c)); }

TEST_CASE("CAC engine: 1-var UNSAT x^2 < 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial xx; xx.addVar(x, 2, 1); xx.normalize();          // x^2
    CacEngine eng(&backend, kernel.get(), {x}, {{xx, Relation::Lt}});   // x^2 < 0
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 1-var UNSAT  x>2 and x<1") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial a; a.addVar(x, 1, 1); a = a + K(-2); a.normalize();   // x - 2
    RationalPolynomial b; b.addVar(x, 1, 1); b = b + K(-1); b.normalize();   // x - 1
    CacEngine eng(&backend, kernel.get(), {x},
                  {{a, Relation::Gt}, {b, Relation::Lt}});                  // x>2 ∧ x<1
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 1-var SAT  x^2 < 4 and x > 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial a; a.addVar(x, 2, 1); a = a + K(-4); a.normalize();   // x^2 - 4
    RationalPolynomial b; b.addVar(x, 1, 1); b.normalize();                  // x
    CacEngine eng(&backend, kernel.get(), {x},
                  {{a, Relation::Lt}, {b, Relation::Gt}});                  // x^2<4 ∧ x>0
    CHECK(eng.solve().status == CacStatus::Sat);
}

TEST_CASE("CAC engine: 2-var UNSAT  x^2+y^2 < 1 and x > 2") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-1); circ.normalize();                                   // x^2+y^2-1
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg = xg + K(-2); xg.normalize(); // x-2
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}});
    CHECK(eng.solve().status == CacStatus::Unsat);
}

TEST_CASE("CAC engine: 2-var SAT  x^2+y^2 < 4 and x > 0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-4); circ.normalize();                                   // x^2+y^2-4
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg.normalize();               // x
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}});
    CHECK(eng.solve().status == CacStatus::Sat);
}

// ---- UNSAT core / origins tracking (task P5 foundation) --------------------
// CacResult::unsatCore lists the constraint indices that DELINEATED the gap-free
// covering. Used to minimize the learned conflict (XOLVER_NRA_CAC_MIN_CONFLICT)
// and, under combination, to carry the interface-(dis)eq lits that participated.
// Contract: on UNSAT it is non-empty, a subset of valid indices, and the
// sub-conjunction over those indices is itself UNSAT (so the lemma stays sound).

TEST_CASE("CAC engine: unsatCore is the single relevant constraint (x^2<0)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial xx; xx.addVar(x, 2, 1); xx.normalize();          // x^2
    CacEngine eng(&backend, kernel.get(), {x}, {{xx, Relation::Lt}});   // x^2 < 0
    CacResult r = eng.solve();
    CHECK(r.status == CacStatus::Unsat);
    CHECK(r.unsatCore == std::vector<size_t>{0});                       // exactly the one constraint
}

TEST_CASE("CAC engine: unsatCore covers both bounds (x>2 and x<1)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    RationalPolynomial a; a.addVar(x, 1, 1); a = a + K(-2); a.normalize();   // x - 2
    RationalPolynomial b; b.addVar(x, 1, 1); b = b + K(-1); b.normalize();   // x - 1
    CacEngine eng(&backend, kernel.get(), {x},
                  {{a, Relation::Gt}, {b, Relation::Lt}});                  // x>2 ∧ x<1
    CacResult r = eng.solve();
    CHECK(r.status == CacStatus::Unsat);
    CHECK(r.unsatCore == std::vector<size_t>{0, 1});                        // both bounds needed
}

TEST_CASE("CAC engine: unsatCore non-empty + in-range on a 2-var UNSAT") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-1); circ.normalize();                                   // x^2+y^2-1
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg = xg + K(-2); xg.normalize(); // x-2
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}});               // x^2+y^2<1 ∧ x>2
    CacResult r = eng.solve();
    CHECK(r.status == CacStatus::Unsat);
    CHECK_FALSE(r.unsatCore.empty());
    for (size_t idx : r.unsatCore) CHECK(idx < 2);                           // valid indices only
    // x>2 (idx 1) is the binding constraint — it MUST appear (the covering of
    // x rules out x>2 entirely; without it the system is sat).
    CHECK(std::find(r.unsatCore.begin(), r.unsatCore.end(), size_t{1}) != r.unsatCore.end());
}

// ---- Early infeasibility probe (Track 1 #39) -------------------------------
// XOLVER_NRA_CAC_EARLY_INFEAS / Config::earlyInfeas: at non-leaf levels, signAt
// every constraint whose mainLevel ≤ current level; a definite-nonzero violation
// excludes the cell on var without recursing. Soundness: SAT unchanged (the
// probe only PRUNES); UNSAT verdict matches the baseline; signAt = Zero
// (nullification) is NOT treated as a violation, it falls through to the
// existing characterize / Lazard-residual path.

TEST_CASE("CAC engine: early-infeas preserves UNSAT verdict + core (2-var)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-1); circ.normalize();                                   // x^2+y^2-1
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg = xg + K(-2); xg.normalize(); // x-2
    CacEngine::Config cfg; cfg.earlyInfeas = true;
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}}, cfg);
    CacResult r = eng.solve();
    CHECK(r.status == CacStatus::Unsat);
    CHECK_FALSE(r.unsatCore.empty());
    // x-2>0 (idx 1) MUST appear (the early-infeas probe at level 0 excludes the
    // x<2 cell directly from this constraint).
    CHECK(std::find(r.unsatCore.begin(), r.unsatCore.end(), size_t{1}) != r.unsatCore.end());
}

TEST_CASE("CAC engine: early-infeas preserves SAT verdict (2-var)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    RationalPolynomial circ; circ.addVar(x, 2, 1); circ.addVar(y, 2, 1);
    circ = circ + K(-4); circ.normalize();                                   // x^2+y^2-4
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg.normalize();               // x
    CacEngine::Config cfg; cfg.earlyInfeas = true;
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{circ, Relation::Lt}, {xg, Relation::Gt}}, cfg);
    CHECK(eng.solve().status == CacStatus::Sat);   // SAT pruning-invariant
}

TEST_CASE("CAC engine: early-infeas + var-independent unsat constraint (whole-axis)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend backend(kernel.get());
    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    // x-5>0 ∧ x+1<0 — both depend only on x (level 0); jointly UNSAT.
    // At level 0 (x), sampling any x value lets early-infeas decide one of the
    // bounds (or both, depending on sample), without ever recursing into y.
    RationalPolynomial xg; xg.addVar(x, 1, 1); xg = xg + K(-5); xg.normalize(); // x-5
    RationalPolynomial xl; xl.addVar(x, 1, 1); xl = xl + K(1);  xl.normalize(); // x+1
    CacEngine::Config cfg; cfg.earlyInfeas = true;
    CacEngine eng(&backend, kernel.get(), {x, y},
                  {{xg, Relation::Gt}, {xl, Relation::Lt}}, cfg);
    CacResult r = eng.solve();
    CHECK(r.status == CacStatus::Unsat);
    CHECK(r.unsatCore == std::vector<size_t>{0, 1});                       // both x-bounds needed
}

#endif  // XOLVER_HAS_LIBPOLY
