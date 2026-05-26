// Backend Lazard tower lift: isolateRealRootsViaTower on a GENUINE two-generator
// tower Q(sqrt2, sqrt3) — the >=2 algebraic-coordinate case that ViaNorm punts
// on. Soundness: keep only the roots of p at the real embedding (drop conjugate
// branches); any inconclusive candidate => supported=false (never UNSAT).

#include <doctest/doctest.h>
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace zolver;

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
