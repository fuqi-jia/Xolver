// [H4] temporary diagnostic: does threading a libpoly kernel into the Lazard
// projection closure recover completion on multivariate inputs with repeated
// factors + non-trivial content, where the hand-rolled subresultant GCD path
// returns ProjectionKernelFailure?
//
// This is a measurement harness, not a permanent regression. It builds a few
// representative multivariate constraint sets and reports the closure-completion
// verdict + wall time with kernel == nullptr (hand-rolled) vs kernel != nullptr
// (libpoly-exact). The fix WORKS iff the kernel path completes >= the
// hand-rolled path (and ideally faster on the degenerate cases).

#include <doctest/doctest.h>
#include <gmpxx.h>

#include <chrono>

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/lazard/LazardProjectionClosure.h"

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

namespace {

// ((x - 2y)(x + 3y))^k * (content in y,z): repeated factor (needs squarefree)
// AND a non-trivial content (needs gcd) — the two ops [H4] routes to libpoly.
RationalPolynomial densePoly(VarId x, VarId y, VarId z, int k, int dy) {
    RationalPolynomial f1; f1.addVar(x, 1, 1); f1.addVar(y, 1, -2); f1.normalize();
    RationalPolynomial f2; f2.addVar(x, 1, 1); f2.addVar(y, 1, 3);  f2.normalize();
    RationalPolynomial base = f1 * f2; base.normalize();
    RationalPolynomial p = base;
    for (int i = 1; i < k; ++i) { p = p * base; p.normalize(); }
    RationalPolynomial cont; cont.addVar(y, dy, 1); cont.addVar(z, 1, 1); cont.addConstant(1);
    cont.normalize();
    p = p * cont; p.normalize();
    return p;
}

struct Outcome { bool complete; double ms; };

Outcome buildOnce(const std::vector<RationalPolynomial>& polys,
                  const std::vector<VarId>& order, PolynomialKernel* kernel) {
    LazardProjectionClosure cl;
    LazardProjectionClosure::Config cfg;
    auto t0 = std::chrono::steady_clock::now();
    auto reason = cl.build(polys, order, cfg, kernel);
    auto t1 = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    return {reason == LazardIncompleteReason::None, ms};
}

}  // namespace

TEST_CASE("[H4] libpoly kernel vs hand-rolled Lazard closure completion (multivar, repeated factors)") {
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId z = kernel.getOrCreateVar("z");
    VarId y = kernel.getOrCreateVar("y");
    VarId x = kernel.getOrCreateVar("x");
    std::vector<VarId> order{z, y, x};

    int handComplete = 0, kernelComplete = 0, total = 0;
    double handMs = 0, kernelMs = 0;

    // ONE representative case (k=2 => deg_x 4, dy=1): the hand-rolled O(n!) path
    // is slow even here, so a single comparison keeps this a unit test (the broad
    // libpoly-vs-hand-rolled validation lives in the differential, not here).
    for (int k = 2; k <= 2; ++k) {
        for (int dy = 1; dy <= 1; ++dy) {
            RationalPolynomial p = densePoly(x, y, z, k, dy);
            RationalPolynomial q = densePoly(x, y, z, k, dy);
            q.addVar(z, 2, 1); q.normalize();
            std::vector<RationalPolynomial> polys{p, q};
            ++total;

            Outcome hand = buildOnce(polys, order, nullptr);
            Outcome kern = buildOnce(polys, order, &kernel);
            handComplete += hand.complete; kernelComplete += kern.complete;
            handMs += hand.ms; kernelMs += kern.ms;
            MESSAGE("k=" << k << " dy=" << dy
                    << "  hand=" << (hand.complete ? "COMPLETE" : "FAIL") << "(" << hand.ms << "ms)"
                    << "  kernel=" << (kern.complete ? "COMPLETE" : "FAIL") << "(" << kern.ms << "ms)");
        }
    }
    MESSAGE("[H4] TOTAL  hand-rolled complete=" << handComplete << " (" << handMs << "ms)"
            << "  libpoly-kernel complete=" << kernelComplete << " (" << kernelMs << "ms)"
            << "  / total=" << total);
    CHECK(kernelComplete >= handComplete);
}

#endif  // XOLVER_HAS_LIBPOLY
