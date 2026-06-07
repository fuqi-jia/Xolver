// Regression tests for NRA step 2.1 — box-consistency GLOBAL refutation
// (CdcacCore::topLevelBoxInfeasible + the degree-2 / general-quadratic contraction
// in propagateBox). These lock in the hong-family win (the box-ICP cracks the
// textbook "CAD fails / NLSAT wins" benchmark) and guard against soundness or
// completeness regressions: every UNSAT here is a genuine bound contradiction,
// every SAT case must NOT be wrongly refuted.
#include <doctest/doctest.h>
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace xolver;

namespace {
// Build x²+y² (+ optional −1) and x·y polys for a 2-var bound-contradiction setup.
struct TwoVar {
    std::unique_ptr<PolynomialKernel> kernel;
    std::unique_ptr<LibpolyBackend> backend;
    VarId x, y;
    PolyId xP, yP, sumSq, prod;
    explicit TwoVar()
        : kernel(createPolynomialKernel()) {
        backend = std::make_unique<LibpolyBackend>(kernel.get());
        x = kernel->getOrCreateVar("x");
        y = kernel->getOrCreateVar("y");
        xP = kernel->mkVar(x);
        yP = kernel->mkVar(y);
        sumSq = kernel->add(kernel->pow(xP, 2), kernel->pow(yP, 2));  // x²+y²
        prod  = kernel->mul(xP, yP);                                  // x·y
    }
    static CdcacConstraint mkC(PolyId poly, Relation rel, int reasonId) {
        CdcacConstraint c;
        c.poly = poly;
        c.rel = rel;
        c.reason = SatLit::positive(reasonId);
        return c;
    }
    CdcacInput input(std::vector<CdcacConstraint> cs) {
        CdcacInput in;
        in.constraints = std::move(cs);
        in.varOrder = {x, y};
        return in;
    }
    PolyId sub1(PolyId p) { return kernel->sub(p, kernel->mkConst(mpq_class(1))); }
};
}  // namespace

TEST_CASE("box-refute: hong-2 (x²+y²<1 ∧ x·y>1) -> UNSAT by bound contradiction") {
    TwoVar t;
    CdcacCore core(t.kernel.get(), t.backend.get());
    // x²+y²−1 < 0  ∧  x·y−1 > 0
    auto in = t.input({TwoVar::mkC(t.sub1(t.sumSq), Relation::Lt, 1),
                       TwoVar::mkC(t.sub1(t.prod),  Relation::Gt, 2)});
    // The global box-consistency check alone proves it: |x|<1,|y|<1 ⇒ |x·y|<1.
    CHECK(core.topLevelBoxInfeasible(in));
    CHECK(core.solve(in).status == CdcacStatus::Unsat);
}

TEST_CASE("box-refute: general quadratic x²-2x+2<0 -> UNSAT (b≠0 contraction)") {
    TwoVar t;
    CdcacCore core(t.kernel.get(), t.backend.get());
    // x²−2x+2 = (x−1)²+1 < 0 is infeasible. Completing the square (s=−1, D=1) gives
    // (x+s)² ≤ −D/c2 = −1 < 0 ⇒ refuted by the box-ICP. y²<1 only makes it 2-var so
    // solve() exercises the early box-refute stage (the ≥2-var gate). c0 here is the
    // CONSTANT 2 (no cross term), so the contraction triggers in round 1.
    PolyId twoX = t.kernel->mul(t.kernel->mkConst(mpq_class(2)), t.xP);
    PolyId xq = t.kernel->add(t.kernel->sub(t.kernel->pow(t.xP, 2), twoX),
                              t.kernel->mkConst(mpq_class(2)));   // x²−2x+2
    auto in = t.input({TwoVar::mkC(xq, Relation::Lt, 1),
                       TwoVar::mkC(t.sub1(t.kernel->pow(t.yP, 2)), Relation::Lt, 2)});  // y²−1<0
    CHECK(core.topLevelBoxInfeasible(in));
    CHECK(core.solve(in).status == CdcacStatus::Unsat);
}

TEST_CASE("box-refute: SAT case x²+y²<1 ∧ x·y>-1 must NOT be refuted") {
    TwoVar t;
    CdcacCore core(t.kernel.get(), t.backend.get());
    // x=y=0 satisfies both: 0<1 and 0>-1. The box-ICP must not wrongly refute.
    PolyId prodPlus1 = t.kernel->add(t.prod, t.kernel->mkConst(mpq_class(1)));  // x·y+1
    auto in = t.input({TwoVar::mkC(t.sub1(t.sumSq), Relation::Lt, 1),
                       TwoVar::mkC(prodPlus1,       Relation::Gt, 2)});
    CHECK_FALSE(core.topLevelBoxInfeasible(in));            // no false bound contradiction
    CHECK(core.solve(in).status == CdcacStatus::Sat);
}

TEST_CASE("box-refute: univariate is NOT shortcut by the box check (≥2-var gate)") {
    // A single-variable problem keeps its covering certificate (the box short-circuit
    // is gated to ≥2 vars). x²<0 is UNSAT but must go through the covering, not the box.
    auto kernel = createPolynomialKernel();
    auto backend = std::make_unique<LibpolyBackend>(kernel.get());
    CdcacCore core(kernel.get(), backend.get());
    VarId x = kernel->getOrCreateVar("x");
    PolyId x2 = kernel->pow(kernel->mkVar(x), 2);
    CdcacInput in;
    in.constraints.push_back(TwoVar::mkC(x2, Relation::Lt, 1));
    in.varOrder.push_back(x);
    // solve()'s ≥2-var gate makes it SKIP the box shortcut for a univariate problem,
    // so the covering decides it AND keeps the V3 certificate (the box check would not).
    auto res = core.solve(in);
    CHECK(res.status == CdcacStatus::Unsat);
    CHECK(res.coveringCert.has_value());
}
