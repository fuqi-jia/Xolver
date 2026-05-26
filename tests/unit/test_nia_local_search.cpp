#include <doctest/doctest.h>
#include "theory/arith/nia/search/NiaLocalSearch.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace zolver;

namespace {

SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// x^2 + y^2 + c  rel 0   (a sum-of-squares constraint over two vars)
NormalizedNiaConstraint sumOfSquares(PolynomialKernel& kernel,
                                     const std::string& vx, const std::string& vy,
                                     const mpz_class& c, Relation rel, SatLit reason) {
    PolyId x = kernel.mkVar(kernel.getOrCreateVar(vx));
    PolyId y = kernel.mkVar(kernel.getOrCreateVar(vy));
    PolyId poly = kernel.add(kernel.add(kernel.pow(x, 2), kernel.pow(y, 2)),
                             kernel.mkConst(mpq_class(c)));
    return {poly, rel, reason};
}

// single-var quadratic: a*x^2 + b*x + c rel 0
NormalizedNiaConstraint uniQuad(PolynomialKernel& kernel, const std::string& v,
                                const mpz_class& a, const mpz_class& b, const mpz_class& c,
                                Relation rel, SatLit reason) {
    PolyId x = kernel.mkVar(kernel.getOrCreateVar(v));
    PolyId poly = kernel.add(
        kernel.add(kernel.mul(kernel.mkConst(mpq_class(a)), kernel.pow(x, 2)),
                   kernel.mul(kernel.mkConst(mpq_class(b)), x)),
        kernel.mkConst(mpq_class(c)));
    return {poly, rel, reason};
}

// True iff `model` satisfies every constraint exactly (the soundness invariant
// the SLS finder must never violate when it returns a model).
bool modelSatisfies(PolynomialKernel& kernel, const IntegerModel& model,
                    const std::vector<NormalizedNiaConstraint>& cs) {
    for (const auto& c : cs) {
        auto v = kernel.evalInteger(c.poly, model);
        if (!v) return false;
        const mpz_class& val = *v;
        bool ok = false;
        switch (c.rel) {
            case Relation::Eq:  ok = (val == 0); break;
            case Relation::Neq: ok = (val != 0); break;
            case Relation::Lt:  ok = (val < 0);  break;
            case Relation::Leq: ok = (val <= 0); break;
            case Relation::Gt:  ok = (val > 0);  break;
            case Relation::Geq: ok = (val >= 0); break;
        }
        if (!ok) return false;
    }
    return true;
}

} // namespace

// ---------------------------------------------------------------------------
// Capability: SLS finds a satisfying model for a multivariate SAT system whose
// solutions lie outside the deterministic seed window (|x|,|y| up to 8).
// x^2 + y^2 = 100  -> e.g. (6,8),(8,6),(10,0)...
// ---------------------------------------------------------------------------
TEST_CASE("NiaSLS: finds model for x^2+y^2=100") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds; // unbounded

    auto c = sumOfSquares(*kernel, "x", "y", mpz_class(-100), Relation::Eq, mkReason(1));
    auto m = ls.tryFindModelSls({c}, ds);

    REQUIRE(m.has_value());
    CHECK(modelSatisfies(*kernel, *m, {c}));
}

// ---------------------------------------------------------------------------
// Capability: single-var quadratic with a large root, outside seed window.
// x^2 - 100x + 2491 = 0  ->  (x-47)(x-53) = 0  -> x=47 or x=53.
// ---------------------------------------------------------------------------
TEST_CASE("NiaSLS: finds large root of x^2-100x+2491=0") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds;

    auto c = uniQuad(*kernel, "x", mpz_class(1), mpz_class(-100), mpz_class(2491),
                     Relation::Eq, mkReason(1));
    auto m = ls.tryFindModelSls({c}, ds);

    REQUIRE(m.has_value());
    CHECK(modelSatisfies(*kernel, *m, {c}));
}

// ---------------------------------------------------------------------------
// Soundness invariant: whatever SLS returns must exactly satisfy the system.
// x^2 = 2 has no integer solution; SLS (incomplete) must return nullopt and
// must NEVER return a non-satisfying "best" candidate.
// ---------------------------------------------------------------------------
TEST_CASE("NiaSLS: never returns a spurious model (x^2=2)") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds;

    auto c = uniQuad(*kernel, "x", mpz_class(1), mpz_class(0), mpz_class(-2),
                     Relation::Eq, mkReason(1));
    auto m = ls.tryFindModelSls({c}, ds);

    // Either no model, or a model that genuinely satisfies (it can't here).
    CHECK((!m.has_value() || modelSatisfies(*kernel, *m, {c})));
    CHECK_FALSE(m.has_value());
}

// ---------------------------------------------------------------------------
// Determinism: fixed seed => reproducible result (regression stability).
// ---------------------------------------------------------------------------
TEST_CASE("NiaSLS: deterministic under fixed seed") {
    auto kernel = createPolynomialKernel();
    NiaLocalSearch ls(*kernel);
    DomainStore ds;

    auto c = sumOfSquares(*kernel, "x", "y", mpz_class(-100), Relation::Eq, mkReason(1));
    auto m1 = ls.tryFindModelSls({c}, ds, /*seed=*/12345u);
    auto m2 = ls.tryFindModelSls({c}, ds, /*seed=*/12345u);

    REQUIRE(m1.has_value());
    REQUIRE(m2.has_value());
    CHECK(*m1 == *m2);
}
