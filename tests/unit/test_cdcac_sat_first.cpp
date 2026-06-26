#include <doctest/doctest.h>
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"
#include "theory/arith/logics/nra/core/CdcacCore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <cstdlib>
#include <string>
#include <unordered_map>

using namespace xolver;

// ------------------------------------------------------------------
// nlsat-engine STEP A: the SAT-only sample-first model search inside
// CdcacCore (XOLVER_NRA_CAC_SAT_FIRST). These tests exercise the engine
// DIRECTLY (the CLI runs the solve on a worker thread whose std::cerr is
// suppressed, so behaviour can only be observed in-process here).
//
// Soundness contract: SAT is returned ONLY on a full rational point at which
// the exact mpq sign of EVERY constraint satisfies its relation (invariant 1);
// the engine NEVER returns Unsat (it falls through to the projection engine on
// failure). The leaf/forward-check use exactSignAt — pure-mpq term-sum — never
// libpoly coefficient_sgn, so no sign evaluation can SIGSEGV.
// ------------------------------------------------------------------

namespace {
CdcacConstraint mkC(PolyId p, Relation rel, uint32_t satVar) {
    CdcacConstraint c;
    c.poly = p;
    c.rel = rel;
    c.reason = SatLit{satVar, true};
    return c;
}
}  // namespace

TEST_CASE("SAT-first: finds & validates a small rational model (xy=6, x+y=5)") {
    setenv("XOLVER_NRA_CAC_SAT_FIRST", "1", 1);
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    // x*y - 6 = 0  and  x + y - 5 = 0   →  {x,y} = {2,3} (or {3,2})
    PolyId p1 = kernel->add(kernel->mul(kernel->mkVar(x), kernel->mkVar(y)),
                            kernel->mkConst(mpq_class(-6)));
    PolyId p2 = kernel->add(kernel->add(kernel->mkVar(x), kernel->mkVar(y)),
                            kernel->mkConst(mpq_class(-5)));

    CdcacInput in;
    in.varOrder = {x, y};
    in.constraints = {mkC(p1, Relation::Eq, 1), mkC(p2, Relation::Eq, 2)};

    CdcacCore core(kernel.get(), &algebra);
    CdcacResult r = core.solve(in);

    REQUIRE(r.status == CdcacStatus::Sat);
    REQUIRE(r.model.has_value());
    // Independently re-validate the returned model over BOTH constraints.
    const SamplePoint& m = *r.model;
    std::unordered_map<std::string, mpq_class> asg;
    for (size_t i = 0; i < m.varOrder.size(); ++i) {
        REQUIRE(m.values[i].isRational());
        asg[std::string(kernel->varName(m.varOrder[i]))] = m.values[i].rational;
    }
    CHECK(kernel->sgn(p1, asg) == 0);
    CHECK(kernel->sgn(p2, asg) == 0);
    unsetenv("XOLVER_NRA_CAC_SAT_FIRST");
}

TEST_CASE("SAT-first: never returns false SAT on an UNSAT system (x^2 + 1 = 0)") {
    setenv("XOLVER_NRA_CAC_SAT_FIRST", "1", 1);
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    VarId x = kernel->getOrCreateVar("x");
    PolyId p = kernel->add(kernel->pow(kernel->mkVar(x), 2),
                           kernel->mkConst(mpq_class(1)));  // x^2 + 1 = 0 (no real root)

    CdcacInput in;
    in.varOrder = {x};
    in.constraints = {mkC(p, Relation::Eq, 1)};

    CdcacCore core(kernel.get(), &algebra);
    CdcacResult r = core.solve(in);

    // SAT-first must not claim SAT; the projection backstop decides Unsat/Unknown.
    CHECK(r.status != CdcacStatus::Sat);
    unsetenv("XOLVER_NRA_CAC_SAT_FIRST");
}

TEST_CASE("SAT-first: an inequality-only system gets a validated rational model") {
    setenv("XOLVER_NRA_CAC_SAT_FIRST", "1", 1);
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    // x^2 + y^2 - 8 <= 0,  x - 2 >= 0,  -(y) - 2 >= 0  →  x=2, y=-2 region
    PolyId circ = kernel->add(kernel->add(kernel->pow(kernel->mkVar(x), 2),
                                          kernel->pow(kernel->mkVar(y), 2)),
                              kernel->mkConst(mpq_class(-8)));
    PolyId xge = kernel->add(kernel->mkVar(x), kernel->mkConst(mpq_class(-2)));
    PolyId yle = kernel->add(kernel->neg(kernel->mkVar(y)), kernel->mkConst(mpq_class(-2)));

    CdcacInput in;
    in.varOrder = {x, y};
    in.constraints = {mkC(circ, Relation::Leq, 1), mkC(xge, Relation::Geq, 2),
                      mkC(yle, Relation::Geq, 3)};

    CdcacCore core(kernel.get(), &algebra);
    CdcacResult r = core.solve(in);

    REQUIRE(r.status == CdcacStatus::Sat);
    REQUIRE(r.model.has_value());
    const SamplePoint& m = *r.model;
    std::unordered_map<std::string, mpq_class> asg;
    for (size_t i = 0; i < m.varOrder.size(); ++i) {
        REQUIRE(m.values[i].isRational());
        asg[std::string(kernel->varName(m.varOrder[i]))] = m.values[i].rational;
    }
    CHECK(kernel->sgn(circ, asg) <= 0);
    CHECK(kernel->sgn(xge, asg) >= 0);
    CHECK(kernel->sgn(yle, asg) >= 0);
    unsetenv("XOLVER_NRA_CAC_SAT_FIRST");
}
