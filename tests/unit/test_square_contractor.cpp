#include <doctest/doctest.h>
#include "theory/arith/icp/contractors/SquareContractorZ.h"
#include "theory/arith/interval/ReasonedBoxZ.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

// Regression for a false-UNSAT in SquareContractorZ: for the sign=-1 normal
// form (-x^2 + c) REL 0 the contractor must rewrite to "x^2 flip(REL) c"
// keeping c UNCHANGED. A prior `c = -c` turned x^2 = 16 (i.e. -x^2 + 16 = 0)
// into c<0 => a spurious Conflict. Reachable only with XOLVER_NIA_ICP, but a
// hard soundness bug there (false UNSAT under the --allon config).

static SatLit reason(SatVar v) { return SatLit::positive(v); }
static PolyId var(PolynomialKernel& k, const char* n) { return k.mkVar(k.getOrCreateVar(n)); }
static PolyId cst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }

// Build (sign * x^2 + a0) as a PolyId.
static PolyId sqPoly(PolynomialKernel& k, int sign, long a0) {
    PolyId x = var(k, "x");
    PolyId xsq = k.mul(x, x);
    PolyId lead = sign == 1 ? xsq : k.mul(cst(k, -1), xsq);
    return k.add(lead, cst(k, a0));
}

static ContractorResultZ run(PolynomialKernel& k, PolyId poly, Relation rel) {
    IcpConstraint c{std::nullopt, poly, rel, reason(1), TheoryId::NIA};
    SquareContractorZ ctr(c, k);
    ReasonedBoxZ box;  // empty box: matches the real failure (x not pre-bounded)
    return ctr.contract(box);
}

TEST_CASE("SquareContractor: -x^2 + 16 = 0 (x^2=16) contracts, no false conflict") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, -1, 16), Relation::Eq);
    REQUIRE(r.status == IcpStatus::DomainUpdate);
    REQUIRE(r.updates.size() == 1);
    CHECK(r.updates[0].newInterval.lo == mpz_class(-4));
    CHECK(r.updates[0].newInterval.hi == mpz_class(4));
}

TEST_CASE("SquareContractor: x^2 - 16 = 0 (sign=1) contracts to [-4,4]") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, 1, -16), Relation::Eq);
    REQUIRE(r.status == IcpStatus::DomainUpdate);
    REQUIRE(r.updates.size() == 1);
    CHECK(r.updates[0].newInterval.lo == mpz_class(-4));
    CHECK(r.updates[0].newInterval.hi == mpz_class(4));
}

TEST_CASE("SquareContractor: -x^2 + 16 >= 0 (x^2<=16) contracts to [-4,4]") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, -1, 16), Relation::Geq);
    REQUIRE(r.status == IcpStatus::DomainUpdate);
    REQUIRE(r.updates.size() == 1);
    CHECK(r.updates[0].newInterval.lo == mpz_class(-4));
    CHECK(r.updates[0].newInterval.hi == mpz_class(4));
}

TEST_CASE("SquareContractor: -x^2 - 1 = 0 (x^2=-1) stays a genuine Conflict") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, -1, -1), Relation::Eq);
    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("SquareContractor: -x^2 + 15 = 0 (non-perfect square) is a Conflict") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, -1, 15), Relation::Eq);
    CHECK(r.status == IcpStatus::Conflict);
}

TEST_CASE("SquareContractor: x^2 = 0 contracts to [0,0]") {
    auto k = createPolynomialKernel();
    auto r = run(*k, sqPoly(*k, -1, 0), Relation::Eq);
    REQUIRE(r.status == IcpStatus::DomainUpdate);
    REQUIRE(r.updates.size() == 1);
    CHECK(r.updates[0].newInterval.lo == mpz_class(0));
    CHECK(r.updates[0].newInterval.hi == mpz_class(0));
}
