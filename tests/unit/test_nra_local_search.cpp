#include <doctest/doctest.h>
#include "theory/arith/nra/reasoners/NraLocalSearch.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <chrono>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// =============================================================================
// Phase A scaffold contract
// =============================================================================

TEST_CASE("NraLocalSearch: empty input returns nullopt") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    REQUIRE_FALSE(ls.tryFindModel({}, {}).has_value());
}

TEST_CASE("NraLocalSearch: trivially-satisfied constraint set returns model at 0") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    // x ≤ 1 is satisfied at x = 0 (LS initial assignment).
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    PolyId poly = kernel->sub(x, kernel->mkConst(mpq_class(1)));   // x − 1
    NraLocalSearch::Constraint c{poly, Relation::Leq, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    CHECK((*m)[vx] == 0);
}

// =============================================================================
// Degree-1 univariate boundary candidate generation
// =============================================================================

TEST_CASE("NraLocalSearch: solves linear strict inequality x > 3") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    // (x − 3) > 0
    PolyId poly = kernel->sub(x, kernel->mkConst(mpq_class(3)));
    NraLocalSearch::Constraint c{poly, Relation::Gt, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    // boundary generator produces root=3 + offset; seed pool includes 1,2,3 too
    // — any value > 3 is acceptable.
    CHECK((*m)[vx] > 3);
}

// =============================================================================
// Degree-2 quadratic discriminant path (the nra_140 x²=2 pattern)
// =============================================================================

TEST_CASE("NraLocalSearch: solves x^2 − 4 = 0 (degree-2 exact roots ±2)") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(4)));
    NraLocalSearch::Constraint c{poly, Relation::Eq, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    const mpq_class v = (*m)[vx];
    CHECK((v == 2 || v == -2));
}

// =============================================================================
// Bracket-pair midpoint (the sprint 5 unlock)
// =============================================================================

TEST_CASE("NraLocalSearch: solves tight bracket pi ∈ (3.1415926, 3.1415927)") {
    // The exact meti-tarski-sqrt-cluster pattern: paired linear bounds 10⁻⁷
    // apart with midpoint denom 2·10⁷ — bracket-midpoint mechanism must
    // produce the satisfier; seed pool + perturbations alone cannot.
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vp = kernel->getOrCreateVar("pi");
    PolyId p = kernel->mkVar(vp);
    // Use simpler tight bracket first to isolate any value-magnitude issue:
    // pi > 1 ∧ pi < 2. Midpoint 3/2 (denom 2).
    // Atoms enter the solver after denominator clearing — `pi > 15707963/5000000`
    // becomes `5000000*pi - 15707963 > 0` (integer-coefficient form). Mirror
    // that here.
    PolyId p5M = kernel->mul(p, kernel->mkConst(mpq_class(5000000)));
    PolyId loPoly = kernel->sub(p5M, kernel->mkConst(mpq_class(15707963)));
    PolyId p10M = kernel->mul(p, kernel->mkConst(mpq_class(10000000)));
    PolyId hiPoly = kernel->sub(p10M, kernel->mkConst(mpq_class(31415927)));
    const mpq_class lo(mpz_class(15707963), mpz_class(5000000));
    const mpq_class hi(mpz_class(31415927), mpz_class(10000000));
    std::vector<NraLocalSearch::Constraint> cs = {
        {loPoly, Relation::Gt, mkReason(1)},
        {hiPoly, Relation::Lt, mkReason(2)},
    };
    auto m = ls.tryFindModel(cs, {vp});
    REQUIRE(m.has_value());
    const mpq_class v = (*m)[vp];
    CHECK(v > lo);
    CHECK(v < hi);
}

// =============================================================================
// Multi-variable composition
// =============================================================================

TEST_CASE("NraLocalSearch: composes per-var moves (x > 1 ∧ y < 5 ∧ x < y)") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(vx);
    PolyId y = kernel->mkVar(vy);
    // x > 1, y < 5, x < y
    PolyId p1 = kernel->sub(x, kernel->mkConst(mpq_class(1)));        // x − 1 > 0
    PolyId p2 = kernel->sub(y, kernel->mkConst(mpq_class(5)));        // y − 5 < 0
    PolyId p3 = kernel->sub(x, y);                                    // x − y < 0
    std::vector<NraLocalSearch::Constraint> cs = {
        {p1, Relation::Gt, mkReason(1)},
        {p2, Relation::Lt, mkReason(2)},
        {p3, Relation::Lt, mkReason(3)},
    };
    auto m = ls.tryFindModel(cs, {vx, vy});
    REQUIRE(m.has_value());
    CHECK((*m)[vx] > 1);
    CHECK((*m)[vy] < 5);
    CHECK((*m)[vx] < (*m)[vy]);
}

// =============================================================================
// Equality relaxation (Phase B) — strict equality still found, relax-flag off
// =============================================================================

TEST_CASE("NraLocalSearch: equality x − 3 = 0 found exactly (no eqRelax)") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    PolyId poly = kernel->sub(x, kernel->mkConst(mpq_class(3)));
    NraLocalSearch::Constraint c{poly, Relation::Eq, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    CHECK((*m)[vx] == 3);
}

TEST_CASE("NraLocalSearch: eqRelax flag accepts a model within ε-band") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    ls.setEqRelax(true);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    // (x − 3) = 0 with EqRelax should still produce x = 3 via boundary or
    // restoration; the contract is "model satisfies relaxed predicate". We
    // verify the returned model's evaluation is within ε of 0.
    PolyId poly = kernel->sub(x, kernel->mkConst(mpq_class(3)));
    NraLocalSearch::Constraint c{poly, Relation::Eq, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    const mpq_class v = (*m)[vx];
    mpq_class err = v - 3;
    if (err < 0) err = -err;
    CHECK(err <= mpq_class(1, 1024));   // default epsilon
}

// =============================================================================
// Soundness: when no rational candidate satisfies (genuinely needs algebraic),
// LS returns nullopt rather than fabricating a wrong answer.
// =============================================================================

TEST_CASE("NraLocalSearch: x^2 = 3 — no exact rational satisfier, returns nullopt") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(3)));
    NraLocalSearch::Constraint c{poly, Relation::Eq, mkReason(1)};
    // No rational q satisfies q² = 3 exactly, so strict-equality LS must NOT
    // produce a model. (sqrt(3) is irrational.)
    auto m = ls.tryFindModel({c}, {vx});
    CHECK_FALSE(m.has_value());
}

// =============================================================================
// Disequality
// =============================================================================

TEST_CASE("NraLocalSearch: x ≠ 0 — initial-zero NOT accepted, finds nonzero") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    NraLocalSearch::Constraint c{x, Relation::Neq, mkReason(1)};
    auto m = ls.tryFindModel({c}, {vx});
    REQUIRE(m.has_value());
    CHECK((*m)[vx] != 0);
}

// =============================================================================
// Budget bound: LS must not run unbounded on a hard case.
// =============================================================================

TEST_CASE("NraLocalSearch: per-call budget cap halts the search on hard input") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    ls.setBudgetMs(5);     // 5ms cap
    ls.setMaxRounds(10);
    // x² = 5 — no rational satisfier. LS must exit within budget.
    VarId vx = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(vx);
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(5)));
    NraLocalSearch::Constraint c{poly, Relation::Eq, mkReason(1)};
    const auto t0 = std::chrono::steady_clock::now();
    auto m = ls.tryFindModel({c}, {vx});
    const auto t1 = std::chrono::steady_clock::now();
    const long ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();
    CHECK_FALSE(m.has_value());        // no rational satisfier
    CHECK(ms <= 500);                   // bounded by budget × a few rounds
}

// =============================================================================
// Top-k var selection: large var sets don't break the contract
// =============================================================================

TEST_CASE("NraLocalSearch: handles 20 vars without iterating all per round") {
    auto kernel = createPolynomialKernel();
    NraLocalSearch ls(*kernel);
    std::vector<VarId> vars;
    std::vector<NraLocalSearch::Constraint> cs;
    // x_0 > 0; the other 19 vars are unconstrained — the top-k selector
    // must focus on the relevant var or LS still solves.
    for (int i = 0; i < 20; ++i) {
        VarId vi = kernel->getOrCreateVar("x" + std::to_string(i));
        vars.push_back(vi);
    }
    PolyId x0 = kernel->mkVar(vars[0]);
    cs.push_back({x0, Relation::Gt, mkReason(1)});
    auto m = ls.tryFindModel(cs, vars);
    REQUIRE(m.has_value());
    CHECK((*m)[vars[0]] > 0);
}
