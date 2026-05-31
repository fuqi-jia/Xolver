#include <doctest/doctest.h>
#include "theory/arith/nia/search/NiaLocalSearch.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// The per-call time cap must not break finding an easy SAT model. x^2 - 4 = 0
// with x in [0,5] has the model x = 2; local search must still return it.
TEST_CASE("NiaLocalSearch: finds easy model x^2-4=0, x in [0,5] (cap intact)") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(4)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 2);
}

// Even with the default budget, an easy model is found (budget is generous
// relative to a tiny search). Also verifies setBudgetMs unlimited path.
TEST_CASE("NiaLocalSearch: unlimited budget still finds the easy model") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setBudgetMs(0);   // unlimited
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId poly = kernel->sub(kernel->pow(x, 2), kernel->mkConst(mpq_class(4)));
    NormalizedNiaConstraint c{poly, Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 2);
}

// Enhanced WalkSAT (XOLVER_NIA_LOCALSEARCH) finds a model the basic ±[-3,3]
// sweep misses: x*y = 12 and x + y = 7 have model {3,4}/{4,3}, with a
// coordinate (4) outside the basic 2-var window. The accelerated critical move
// jumps there. (Candidate-only; soundness is the caller's validator, so the
// returned model must satisfy both constraints.)
TEST_CASE("NiaLocalSearch enhanced: x*y=12 & x+y=7 -> finds {3,4}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setBudgetMs(0);  // unlimited for the test
    DomainStore ds;     // unbounded vars

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    NormalizedNiaConstraint prod{kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(12))),
                                 Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint sum{kernel->sub(kernel->add(x, y), kernel->mkConst(mpq_class(7))),
                                Relation::Eq, mkReason(2)};

    auto m = ls.tryFindModel({prod, sum}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"], yv = (*m)["y"];
    CHECK(xv * yv == 12);
    CHECK(xv + yv == 7);
}

// ---------- Phase L1: LS-IA + Yices2LS-style enhancements ----------

// Same SAT system the base enhanced WalkSAT solves — pinned: L1 must not
// REGRESS the model-finding contract. The kernel is the same, so a Sat
// result is still a sound witness.
TEST_CASE("NiaLocalSearch L1 (two-level): x*y=12 & x+y=7 -> finds {3,4}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    NormalizedNiaConstraint prod{kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(12))),
                                 Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint sum{kernel->sub(kernel->add(x, y), kernel->mkConst(mpq_class(7))),
                                Relation::Eq, mkReason(2)};

    auto m = ls.tryFindModel({prod, sum}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"], yv = (*m)["y"];
    CHECK(xv * yv == 12);
    CHECK(xv + yv == 7);
}

// Multi-variable system that exercises the incremental score path: 3 vars,
// 4 constraints. Without incremental tracking the original walkSat would
// re-evaluate every clause per candidate try, scaling badly; L1 only re-
// evaluates clauses containing the moved variable. Pinned: L1 finds an
// integer model. (Caller-side validation is the soundness gate; we double-
// check by hand here.)
TEST_CASE("NiaLocalSearch L1 (two-level): 3-var system x+y+z=6, xy=6, yz=12, xz=8") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(1), mkReason(11));
    ds.addUpperBound("x", mpz_class(10), mkReason(12));
    ds.addLowerBound("y", mpz_class(1), mkReason(13));
    ds.addUpperBound("y", mpz_class(10), mkReason(14));
    ds.addLowerBound("z", mpz_class(1), mkReason(15));
    ds.addUpperBound("z", mpz_class(10), mkReason(16));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));
    // Model: (x, y, z) = (2, 3, 4) satisfies x+y+z=9 — adjust target.
    NormalizedNiaConstraint sum{
        kernel->sub(kernel->add(kernel->add(x, y), z), kernel->mkConst(mpq_class(9))),
        Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint xy{
        kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(6))),
        Relation::Eq, mkReason(2)};
    NormalizedNiaConstraint yz{
        kernel->sub(kernel->mul(y, z), kernel->mkConst(mpq_class(12))),
        Relation::Eq, mkReason(3)};
    NormalizedNiaConstraint xz{
        kernel->sub(kernel->mul(x, z), kernel->mkConst(mpq_class(8))),
        Relation::Eq, mkReason(4)};

    auto m = ls.tryFindModel({sum, xy, yz, xz}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"], yv = (*m)["y"], zv = (*m)["z"];
    CHECK(xv + yv + zv == 9);
    CHECK(xv * yv == 6);
    CHECK(yv * zv == 12);
    CHECK(xv * zv == 8);
}

// Soundness pin: even when no model exists (UNSAT system), L1 must return
// nullopt — NEVER claim Sat. The caller's contract is "Sat means valid
// witness or nothing".
TEST_CASE("NiaLocalSearch L1 (two-level): on trivially-UNSAT system, returns nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setBudgetMs(50);   // capped budget — we only want to confirm no-Sat-claim
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(5), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x = 100 ∧ x in [5,10] — no model.
    NormalizedNiaConstraint eq{
        kernel->sub(x, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({eq}, ds);
    CHECK(!m.has_value());  // must NOT claim Sat
}

// ---------- Phase L1 step 2: persistent NiaLsContext (warm-start) ----------

// Warm-start fast-path: first call solves and writes context; second call
// with the SAME constraint set returns the same answer instantly via
// warm-start. The activity counter is bumped on improving moves.
TEST_CASE("NiaLocalSearch L1 step 2 (warm-start): same-signature second call uses context") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setWarmStart(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    NormalizedNiaConstraint prod{kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(12))),
                                 Relation::Eq, mkReason(1)};
    NormalizedNiaConstraint sum{kernel->sub(kernel->add(x, y), kernel->mkConst(mpq_class(7))),
                                Relation::Eq, mkReason(2)};

    auto m1 = ls.tryFindModel({prod, sum}, ds);
    REQUIRE(m1.has_value());
    // After the first call, context should have a signature recorded
    // AND varActivity should have entries (the search committed improving
    // moves on x and y).
    const auto& ctx = ls.lsContext();
    CHECK(ctx.lastSignature != 0);
    CHECK(ctx.bestValid);
    CHECK(!ctx.bestAssignment.empty());
    // Second call with same constraint set — same answer, warm-start
    // returns it immediately.
    auto m2 = ls.tryFindModel({prod, sum}, ds);
    REQUIRE(m2.has_value());
    CHECK((*m2)["x"] * (*m2)["y"] == 12);
    CHECK((*m2)["x"] + (*m2)["y"] == 7);
}

// Signature mismatch correctness pin: if the constraint set changes
// between calls, the cached bestAssignment must be DROPPED (a stale
// assignment from constraint set A can't be reused on constraint set B
// without re-validation). Heuristic state (PAWS weights) may persist.
TEST_CASE("NiaLocalSearch L1 step 2 (warm-start): signature mismatch drops stale assignment") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setWarmStart(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c1{
        kernel->sub(x, kernel->mkConst(mpq_class(42))),
        Relation::Eq, mkReason(1)};  // x = 42

    auto m1 = ls.tryFindModel({c1}, ds);
    REQUIRE(m1.has_value());
    CHECK((*m1)["x"] == 42);

    // Different constraint set: x = 7. Signature MUST mismatch and the
    // cached x=42 assignment MUST be dropped. The model from this call
    // must satisfy the new system.
    NormalizedNiaConstraint c2{
        kernel->sub(x, kernel->mkConst(mpq_class(7))),
        Relation::Eq, mkReason(2)};
    auto m2 = ls.tryFindModel({c2}, ds);
    REQUIRE(m2.has_value());
    CHECK((*m2)["x"] == 7);
}

// resetLsContext() invalidation: explicit reset clears the context so
// the next call starts cold. Needed for solver-side onBacktrack hooks
// that throw away derivation chains.
TEST_CASE("NiaLocalSearch L1 step 2 (warm-start): resetLsContext() clears state") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setWarmStart(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(99))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK(ls.lsContext().bestValid);

    ls.resetLsContext();
    const auto& ctx = ls.lsContext();
    CHECK(!ctx.bestValid);
    CHECK(ctx.bestAssignment.empty());
    CHECK(ctx.clauseWeight.empty());
    CHECK(ctx.varActivity.empty());
    CHECK(ctx.lastSignature == 0);
}

// Soundness pin: warm-start NEVER claims Sat without a fresh validator
// pass. The persistent context can hold a stale assignment that no
// longer satisfies a changed system; tryFindModel must still verify by
// running the search to fixpoint (cost = 0) on the CURRENT constraints,
// not just rubber-stamp the cached bestAssignment.
TEST_CASE("NiaLocalSearch L1 step 2 (warm-start): never rubber-stamps stale cache") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setWarmStart(true);
    ls.setBudgetMs(50);  // tiny budget
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // First call: solve x = 50.
    NormalizedNiaConstraint c1{
        kernel->sub(x, kernel->mkConst(mpq_class(50))),
        Relation::Eq, mkReason(1)};
    auto m1 = ls.tryFindModel({c1}, ds);
    REQUIRE(m1.has_value());

    // Second call: trivially UNSAT, x = 100 ∧ x ∈ [0, 10]. The cached
    // x=50 must NOT be returned (it doesn't even satisfy the second
    // constraint). Signature differs, cache is dropped, LS searches
    // fresh, can't find a model, returns nullopt.
    DomainStore ds2;
    ds2.addLowerBound("x", mpz_class(0), mkReason(2));
    ds2.addUpperBound("x", mpz_class(10), mkReason(3));
    NormalizedNiaConstraint c2{
        kernel->sub(x, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(4)};
    auto m2 = ls.tryFindModel({c2}, ds2);
    CHECK(!m2.has_value());  // must NOT claim sat with stale cache
}

// Warm-start disabled = baseline behavior. Confirms the flag actually
// gates the entire persistence path (e.g. context stays empty).
TEST_CASE("NiaLocalSearch L1 step 2 (warm-start): default-OFF keeps context empty") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    // setWarmStart NOT called → default-OFF
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(33))),
        Relation::Eq, mkReason(1)};
    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    // Context must stay empty when warm-start is off.
    const auto& ctx = ls.lsContext();
    CHECK(!ctx.bestValid);
    CHECK(ctx.bestAssignment.empty());
    CHECK(ctx.lastSignature == 0);
}

// Accelerated step covers a slope-based target far from the initial point.
// Constraint: x = 1000. Initial assignment puts x at 0; the discrete-Newton
// step (slope=1, target -p(0)/slope = 1000) plus the acc=1.2 series should
// quickly jump there. This exercises that L1's adaptive step does the big
// jump that base walkSat could also do.
TEST_CASE("NiaLocalSearch L1 (two-level): accelerated step handles big jump x = 1000") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setBudgetMs(0);
    DomainStore ds;   // unbounded

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint eq{
        kernel->sub(x, kernel->mkConst(mpq_class(1000))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({eq}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 1000);
}
