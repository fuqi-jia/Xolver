#include <doctest/doctest.h>

#include "theory/arith/logics/nia/reasoners/BoundedNiaSolver.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/logics/nia/search/IntegerModelValidator.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"

#include <gmpxx.h>
#include <vector>

// Phase 3a unit tests for BoundedNiaSolver::solvePartial.
//
// Soundness contract under test:
//   - SAT returned ⇔ IntegerModelValidator confirms the candidate model.
//     The validator runs against the EXACT constraint list passed in, so a
//     Valid result is a sound SAT witness against the ORIGINAL system.
//   - Never returns UnsatComplete (unbounded vars' search space isn't
//     exhausted). Always UnknownUnsupported on failure.
//   - Empty bounded subset → UnknownUnsupported (no enumeration to do).

using namespace xolver;

namespace {

SatLit lit(unsigned int v, bool sign = true) { return {v, sign}; }

}

TEST_CASE("BoundedNiaSolver::solvePartial — bounded var + unbounded with 0 guess validates SAT") {
    auto k = createPolynomialKernel();
    if (!k) return;

    // Constraint: x + y = 0  with x ∈ [-1, 1], y unbounded.
    // Candidate model with x = 0, y = 0 should validate.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId sum = k->add(x, y);

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({sum, Relation::Eq, lit(1)});

    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-1), lit(2));
    domains.addUpperBound("x", mpz_class(1), lit(3));
    // y has no bounds.

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartial(cs, domains, validator);

    REQUIRE(res.status == BoundedSolveStatus::Sat);
    REQUIRE(res.model.has_value());
    // Validate the returned model satisfies the original constraint
    // (sum == 0). Don't assume which specific (x, y) pair the enumerator
    // picks — order of iteration is an implementation detail; what
    // matters is that the model is a sound witness.
    const auto& m = *res.model;
    REQUIRE(m.count("x") == 1);
    REQUIRE(m.count("y") == 1);
    CHECK(m.at("x") + m.at("y") == 0);
}

TEST_CASE("BoundedNiaSolver::solvePartial — empty bounded subset returns UnknownUnsupported") {
    auto k = createPolynomialKernel();
    if (!k) return;

    // Both x and y unbounded → no bounded subset → can't apply the lever.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId xy = k->add(x, y);

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({xy, Relation::Eq, lit(1)});

    DomainStore domains;  // no bounds on either var
    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartial(cs, domains, validator);

    CHECK(res.status == BoundedSolveStatus::UnknownUnsupported);
    CHECK(!res.model.has_value());
}

TEST_CASE("BoundedNiaSolver::solvePartial — bounded subset that fails all guesses returns Unknown not Unsat") {
    auto k = createPolynomialKernel();
    if (!k) return;

    // Constraint: x = 5  with x ∈ [-1, 1] (impossible at every bounded
    // value AND every unbounded guess in the residual). Generator MUST
    // NOT claim UnsatComplete — invariant: partial enumeration never
    // returns UnsatComplete (unbounded search space could hold a model
    // even though here there's nothing left to search).
    //
    // We use a second var y unbounded to keep the lever's precondition
    // (some unbounded vars present), so the path under test is the
    // partial path, not the full-enumerate path.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId xMinus5 = k->sub(x, k->mkConst(mpq_class(5)));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({xMinus5, Relation::Eq, lit(1)});  // x = 5
    // Add a trivially-true constraint that references y so y is in varSet.
    PolyId yEqY = k->sub(y, y);  // 0
    cs.push_back({yEqY, Relation::Eq, lit(4)});      // 0 = 0 (vacuous)

    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-1), lit(2));
    domains.addUpperBound("x", mpz_class(1), lit(3));

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartial(cs, domains, validator);

    // No bounded value of x satisfies x = 5; never returns SAT.
    // Critical soundness check: must NOT return UnsatComplete.
    CHECK(res.status == BoundedSolveStatus::UnknownUnsupported);
    CHECK(!res.model.has_value());
}

TEST_CASE("BoundedNiaSolver::solvePartial — bilinear with bounded factor linearizes") {
    auto k = createPolynomialKernel();
    if (!k) return;

    // Constraint: b*y - 7 = 0  with b ∈ [-2, 2], y unbounded.
    // For b = 1: y = 7 (not in default guess set {0,1,-1}).
    // For b = 7: not in domain.
    // So the trivial guess set should miss this... unless one of the
    // bound-anchored guesses happens to match.
    //
    // This test pins what the lever DOES with the guess set: small linear
    // gaps it'll catch (y = 0 makes b*0 - 7 = -7 ≠ 0; y = 7 not in default
    // set; so this CASE doesn't validate). Expected: UnknownUnsupported.
    PolyId b = k->mkVar(k->getOrCreateVar("b"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));
    PolyId by = k->mul(b, y);
    PolyId byMinus7 = k->sub(by, k->mkConst(mpq_class(7)));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({byMinus7, Relation::Eq, lit(1)});

    DomainStore domains;
    domains.addLowerBound("b", mpz_class(-2), lit(2));
    domains.addUpperBound("b", mpz_class(2), lit(3));

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartial(cs, domains, validator);

    // The guess set {0, 1, -1, lo+1, hi-1} = {0, 1, -1} for unbounded y;
    // none of those gives a valid model when combined with any b ∈ [-2, 2].
    // Documents the lever's reach: small fixed guess set ⇒ small reach.
    CHECK(res.status == BoundedSolveStatus::UnknownUnsupported);
}

// ---------- Phase L1 step 3: value-cache hint path ----------

TEST_CASE("BoundedNiaSolver::solvePartialWithHint — valid hint returns Sat in 1 validation") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->add(x, y), k->mkConst(mpq_class(7))),
                  Relation::Eq, lit(1)});
    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-1), lit(2));
    domains.addUpperBound("x", mpz_class(1), lit(3));

    // Hint = {x: 0, y: 7} — valid model for x + y = 7. The hint path
    // returns Sat without cartesian enumeration.
    IntegerModel hint{{"x", mpz_class(0)}, {"y", mpz_class(7)}};

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartialWithHint(cs, domains, validator, &hint);
    REQUIRE(res.status == BoundedSolveStatus::Sat);
    CHECK((*res.model).at("x") == 0);
    CHECK((*res.model).at("y") == 7);
}

TEST_CASE("BoundedNiaSolver::solvePartialWithHint — invalid hint falls through to enumeration") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->add(x, y), k->mkConst(mpq_class(0))),
                  Relation::Eq, lit(1)});  // x + y = 0
    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-1), lit(2));
    domains.addUpperBound("x", mpz_class(1), lit(3));

    // Bogus hint: x=99, y=99. Does NOT satisfy x+y=0. Falls through to
    // the existing enumeration which finds {x=0, y=0} (or similar).
    IntegerModel hint{{"x", mpz_class(99)}, {"y", mpz_class(99)}};

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartialWithHint(cs, domains, validator, &hint);
    REQUIRE(res.status == BoundedSolveStatus::Sat);
    // Result must satisfy the constraint — never the bogus hint.
    CHECK((*res.model).at("x") + (*res.model).at("y") == 0);
    // x must be in [-1, 1] (the bounded subset).
    CHECK((*res.model).at("x") >= -1);
    CHECK((*res.model).at("x") <= 1);
}

TEST_CASE("BoundedNiaSolver::solvePartialWithHint — null hint behaves as legacy solvePartial") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(x, k->mkConst(mpq_class(0))),
                  Relation::Eq, lit(1)});
    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-3), lit(2));
    domains.addUpperBound("x", mpz_class(3), lit(3));

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartialWithHint(cs, domains, validator, nullptr);
    REQUIRE(res.status == BoundedSolveStatus::Sat);
    CHECK((*res.model).at("x") == 0);
}

// Soundness pin: a hint that DOESN'T cover all variables in the
// constraint set is harmless — the fast-path skips, enumeration proceeds.
TEST_CASE("BoundedNiaSolver::solvePartialWithHint — partial-coverage hint skips fast-path") {
    auto k = createPolynomialKernel();
    if (!k) return;
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId y = k->mkVar(k->getOrCreateVar("y"));

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({k->sub(k->add(x, y), k->mkConst(mpq_class(5))),
                  Relation::Eq, lit(1)});
    DomainStore domains;
    domains.addLowerBound("x", mpz_class(0), lit(2));
    domains.addUpperBound("x", mpz_class(5), lit(3));

    // Hint only names x, not y. Fast-path validation skipped; the
    // unbounded-guess loop still PRIORITISES the cached x value.
    IntegerModel hint{{"x", mpz_class(3)}};

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartialWithHint(cs, domains, validator, &hint);
    REQUIRE(res.status == BoundedSolveStatus::Sat);
    CHECK((*res.model).at("x") + (*res.model).at("y") == 5);
}

TEST_CASE("BoundedNiaSolver::solvePartial — fully-bounded system delegates correctly") {
    auto k = createPolynomialKernel();
    if (!k) return;

    // ALL vars bounded. The lever should still work but its niche is the
    // unbounded-residual case. This test pins behavior when there are NO
    // unbounded vars — bounded × empty-unbounded-guess Cartesian product
    // is just bounded enumeration.
    PolyId x = k->mkVar(k->getOrCreateVar("x"));
    PolyId xPoly = k->sub(x, k->mkConst(mpq_class(0)));   // x = 0

    std::vector<NormalizedNiaConstraint> cs;
    cs.push_back({xPoly, Relation::Eq, lit(1)});

    DomainStore domains;
    domains.addLowerBound("x", mpz_class(-3), lit(2));
    domains.addUpperBound("x", mpz_class(3), lit(3));

    IntegerModelValidator validator(*k);
    BoundedNiaSolver solver(*k);
    auto res = solver.solvePartial(cs, domains, validator);

    REQUIRE(res.status == BoundedSolveStatus::Sat);
    CHECK((*res.model).at("x") == 0);
}
