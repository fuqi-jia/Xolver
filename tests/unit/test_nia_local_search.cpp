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

// ---------- Phase L1 P2: multi-scale step ----------

TEST_CASE("NiaLocalSearch L1 P2 (multi-scale): x^2 = 100 finds x = 10 via sqrt target") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setMultiScale(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x² = 100. Without the √|val| target the Newton series struggles;
    // with multi-scale, sqrt(100) = 10 is generated directly.
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->sub(xx, kernel->mkConst(mpq_class(100))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK(xv * xv == 100);
}

TEST_CASE("NiaLocalSearch L1 P2 (multi-scale): doubling reaches x = 1024 far jump") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setMultiScale(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(1024))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 1024);
}

TEST_CASE("NiaLocalSearch L1 P2 (multi-scale): default-OFF uses legacy 6/5 series") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    // setMultiScale NOT called → multi-scale path off
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(7))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 7);
}

TEST_CASE("NiaLocalSearch L1 P2 (multi-scale): handles x*y = N bilinear with multi-scale jump") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setMultiScale(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    // x * y = 256. {16, 16}, {8, 32}, {32, 8} all work.
    NormalizedNiaConstraint c{
        kernel->sub(kernel->mul(x, y), kernel->mkConst(mpq_class(256))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] * (*m)["y"] == 256);
}

// Soundness pin: multi-scale step never finds a Sat that doesn't validate
// against the original system. Same UNSAT case as the two-level test —
// must return nullopt even with multi-scale.
TEST_CASE("NiaLocalSearch L1 P2 (multi-scale): trivially-UNSAT returns nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setMultiScale(true);
    ls.setBudgetMs(50);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(999))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    CHECK(!m.has_value());
}

// ---------- Phase L1 P3: degree ≤ 2 critical move ----------

// Pure-quadratic atom: x² = 25 ⇒ roots ±5. Quad-critical generates them
// directly via the discriminant path.
TEST_CASE("NiaLocalSearch L1 P3 (quad-critical): x^2 = 25 finds root via quadratic path") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setQuadCritical(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->sub(xx, kernel->mkConst(mpq_class(25))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK(xv * xv == 25);
}

// Mixed quadratic: x² + 3x - 10 = 0 ⇒ (x+5)(x-2) = 0, roots {-5, 2}.
TEST_CASE("NiaLocalSearch L1 P3 (quad-critical): x^2 + 3x - 10 = 0 finds {-5, 2}") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setQuadCritical(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    PolyId threex = kernel->mul(kernel->mkConst(mpq_class(3)), x);
    // x² + 3x - 10
    PolyId expr = kernel->sub(kernel->add(xx, threex),
                              kernel->mkConst(mpq_class(10)));
    NormalizedNiaConstraint c{expr, Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK((xv == -5 || xv == 2));
}

// Linear case (a = 0): the quadratic-detect branch sees a = 0 and skips;
// the Newton-step branch below still solves it. Pin that we don't break
// linear handling when quad-critical is on.
TEST_CASE("NiaLocalSearch L1 P3 (quad-critical): linear x = 17 still solved (a=0 falls back)") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setQuadCritical(true);
    ls.setBudgetMs(0);
    DomainStore ds;

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(17))),
        Relation::Eq, mkReason(1)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 17);
}

// Negative discriminant: x² + 1 = 0 has no integer root; LS must NOT
// claim Sat. The quadratic path detects D < 0 and skips.
TEST_CASE("NiaLocalSearch L1 P3 (quad-critical): D<0 (x^2 + 1 = 0) returns nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setQuadCritical(true);
    ls.setBudgetMs(50);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(-10), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->add(xx, kernel->mkConst(mpq_class(1))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    CHECK(!m.has_value());
}

// Default-OFF behavior: quad-critical OFF leaves earlier search paths
// untouched. Tested on the same x² = 25 input that the new path handles.
TEST_CASE("NiaLocalSearch L1 P3 (quad-critical): default-OFF still solves x^2 = 4") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    // setQuadCritical NOT called
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(5), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId xx = kernel->pow(x, 2);
    NormalizedNiaConstraint c{
        kernel->sub(xx, kernel->mkConst(mpq_class(4))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    mpz_class xv = (*m)["x"];
    CHECK(xv * xv == 4);
}

// ---------- Phase L1 P4: feasible-set jump ----------

TEST_CASE("NiaLocalSearch L1 P4 (fs-jump): tight bound x in [42,42] is jumped to directly") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setFsJump(true);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(42), mkReason(1));
    ds.addUpperBound("x", mpz_class(42), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(42))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 42);
}

TEST_CASE("NiaLocalSearch L1 P4 (fs-jump): finite-set domain — iterates set members") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setFsJump(true);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.restrictToFiniteSet("x",
        std::set<mpz_class>{mpz_class(7), mpz_class(13), mpz_class(19)},
        mkReason(1));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x = 13 — must satisfy.
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(13))),
        Relation::Eq, mkReason(2)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 13);
}

TEST_CASE("NiaLocalSearch L1 P4 (fs-jump): default-OFF still solves the same case") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    // setFsJump NOT called
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(42), mkReason(1));
    ds.addUpperBound("x", mpz_class(42), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(42))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 42);
}

TEST_CASE("NiaLocalSearch L1 P4 (fs-jump): excluded values' neighbours are tried") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setFsJump(true);
    ls.setBudgetMs(0);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), mkReason(1));
    ds.addUpperBound("x", mpz_class(10), mkReason(2));
    ds.excludeValue("x", mpz_class(5), mkReason(3));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x = 4 or x = 6 should satisfy (neighbours of the excluded 5).
    NormalizedNiaConstraint c{
        kernel->sub(kernel->mul(x, kernel->mkConst(mpq_class(2))),
                    kernel->mkConst(mpq_class(8))),
        Relation::Eq, mkReason(4)};

    auto m = ls.tryFindModel({c}, ds);
    REQUIRE(m.has_value());
    CHECK((*m)["x"] == 4);
}

TEST_CASE("NiaLocalSearch L1 P4 (fs-jump): contradictory bounds return nullopt") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    ls.setEnhanced(true);
    ls.setTwoLevel(true);
    ls.setFsJump(true);
    ls.setBudgetMs(50);
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(50), mkReason(1));
    ds.addUpperBound("x", mpz_class(50), mkReason(2));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    // x = 999 in domain x = 50 — no model.
    NormalizedNiaConstraint c{
        kernel->sub(x, kernel->mkConst(mpq_class(999))),
        Relation::Eq, mkReason(3)};

    auto m = ls.tryFindModel({c}, ds);
    CHECK(!m.has_value());
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
