// Backend Lazard tower lift: isolateRealRootsViaTower on a GENUINE two-generator
// tower Q(sqrt2, sqrt3) — the >=2 algebraic-coordinate case that ViaNorm punts
// on. Soundness: keep only the roots of p at the real embedding (drop conjugate
// branches); any inconclusive candidate => supported=false (never UNSAT).

#include <doctest/doctest.h>
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace xolver;

namespace {
// Prefix coordinate a = +sqrt2 (defPoly x^2-2, interval [1,2]) in variable `a`.
RealAlg sqrt2In(VarId /*unused*/, LibpolyBackend& algebra) {
    AlgebraicRoot r;
    r.definingPoly = algebra.allocUni({1, 0, -2});   // x^2 - 2
    r.rootIndex = 1; r.lower = mpq_class(1); r.upper = mpq_class(2);
    return RealAlg::fromAlgebraic(r);
}
// Prefix coordinate b = +sqrt3 (defPoly x^2-3, interval [1,2]).
RealAlg sqrt3In(LibpolyBackend& algebra) {
    AlgebraicRoot r;
    r.definingPoly = algebra.allocUni({1, 0, -3});   // x^2 - 3
    r.rootIndex = 1; r.lower = mpq_class(1); r.upper = mpq_class(2);
    return RealAlg::fromAlgebraic(r);
}
}  // namespace

TEST_CASE("ViaTower: p = z - a - b over Q(sqrt2,sqrt3) keeps only z = sqrt2+sqrt3") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId a = kernel->getOrCreateVar("a");
    VarId b = kernel->getOrCreateVar("b");
    VarId z = kernel->getOrCreateVar("z");

    // p = z - a - b ; real root at the embedding is z = sqrt2+sqrt3 ~ 3.146.
    PolyId p = kernel->add(kernel->mkVar(z),
                           kernel->neg(kernel->add(kernel->mkVar(a), kernel->mkVar(b))));

    SamplePoint prefix;
    prefix.push(a, sqrt2In(a, algebra));
    prefix.push(b, sqrt3In(algebra));

    bool supported = false;
    RootSet roots = algebra.isolateRealRootsViaTower(p, prefix, z, supported);
    CHECK(supported);
    // Norm is degree 4 with roots +-sqrt2+-sqrt3; only one (sqrt2+sqrt3) is a
    // root of p at this branch — the other three conjugates must be dropped.
    CHECK(roots.numRoots() == 1);
}

TEST_CASE("ViaTower: p = z^2 + a + b has NO real root at the embedding => 0 roots") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId a = kernel->getOrCreateVar("a");
    VarId b = kernel->getOrCreateVar("b");
    VarId z = kernel->getOrCreateVar("z");

    // z^2 + a + b ; at a=sqrt2, b=sqrt3 this is z^2 + 3.146 > 0 (no real root).
    PolyId p = kernel->add(kernel->pow(kernel->mkVar(z), 2),
                           kernel->add(kernel->mkVar(a), kernel->mkVar(b)));

    SamplePoint prefix;
    prefix.push(a, sqrt2In(a, algebra));
    prefix.push(b, sqrt3In(algebra));

    bool supported = false;
    RootSet roots = algebra.isolateRealRootsViaTower(p, prefix, z, supported);
    CHECK(supported);
    CHECK(roots.numRoots() == 0);   // all conjugate-branch Norm roots dropped
}

TEST_CASE("ViaTower: nullifying p = (a^2-2)*z at a=sqrt2 recovers residual root z=0") {
    // p = (a^2 - 2)*z. At a = sqrt2 the substitution makes p vanish IDENTICALLY
    // (a^2 -> 2), so the Norm degenerates to a constant. The T2 valuation path
    // recovers the Lazard residual d/da[(a^2-2)z] = 2*a*z, whose only real root
    // in z (at a=sqrt2 != 0) is z = 0. This exercises the nullification branch
    // wired into isolateRealRootsViaTower.
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId a = kernel->getOrCreateVar("a");
    VarId z = kernel->getOrCreateVar("z");

    // (a^2 - 2) * z
    PolyId a2m2 = kernel->add(kernel->pow(kernel->mkVar(a), 2),
                              kernel->mkConst(mpq_class(-2)));
    PolyId p = kernel->mul(a2m2, kernel->mkVar(z));

    SamplePoint prefix;
    prefix.push(a, sqrt2In(a, algebra));

    bool supported = false;
    RootSet roots = algebra.isolateRealRootsViaTower(p, prefix, z, supported);
    CHECK(supported);
    REQUIRE(roots.numRoots() == 1);
    CHECK(roots.roots[0].isRational());
    CHECK(roots.roots[0].rational == mpq_class(0));
}

TEST_CASE("ViaTower: nullifying p=(a^2-2)*(z-a) at a=sqrt2 recovers residual root z=sqrt2") {
    // p = (a^2-2)*(z-a). Nullifies at a=sqrt2. Residual d/da = 2a*(z-a) + (a^2-2)*(-1);
    // the second term reduces to 0 mod m, leaving 2a*(z-a) = 2a*z - 2a^2 -> (reduce
    // a^2->2) 2a*z - 4. Its root in z is z = 4/(2a) = 2/a = 2/sqrt2 = sqrt2. So the
    // single surviving real root is z = sqrt2 (~1.414); the conjugate -sqrt2 (from
    // the Norm) must be dropped by the exact membership filter.
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId a = kernel->getOrCreateVar("a");
    VarId z = kernel->getOrCreateVar("z");

    PolyId a2m2 = kernel->add(kernel->pow(kernel->mkVar(a), 2),
                              kernel->mkConst(mpq_class(-2)));
    PolyId zma = kernel->add(kernel->mkVar(z), kernel->neg(kernel->mkVar(a)));
    PolyId p = kernel->mul(a2m2, zma);

    SamplePoint prefix;
    prefix.push(a, sqrt2In(a, algebra));

    bool supported = false;
    RootSet roots = algebra.isolateRealRootsViaTower(p, prefix, z, supported);
    CHECK(supported);
    REQUIRE(roots.numRoots() == 1);
    // z = sqrt2 ~ 1.414 : isolating interval must straddle it (and not -sqrt2).
    const auto& r0 = roots.roots[0];
    if (r0.isRational()) { CHECK(r0.rational > mpq_class(1)); }
    else { CHECK(r0.root.lower > mpq_class(0)); CHECK(r0.root.upper < mpq_class(2)); }
}

TEST_CASE("ViaTower: single algebraic coord still works (a=sqrt2, p=z-a)") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());
    VarId a = kernel->getOrCreateVar("a");
    VarId z = kernel->getOrCreateVar("z");

    PolyId p = kernel->add(kernel->mkVar(z), kernel->neg(kernel->mkVar(a)));   // z - a

    SamplePoint prefix;
    prefix.push(a, sqrt2In(a, algebra));

    bool supported = false;
    RootSet roots = algebra.isolateRealRootsViaTower(p, prefix, z, supported);
    CHECK(supported);
    CHECK(roots.numRoots() == 1);   // z = +sqrt2 kept, -sqrt2 dropped
}
