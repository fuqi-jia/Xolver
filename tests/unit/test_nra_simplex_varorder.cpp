#include <doctest/doctest.h>
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <set>
#include <algorithm>

using namespace zolver;

static CdcacConstraint mkC(PolyId p, Relation r, int litVar) {
    CdcacConstraint c;
    c.poly = p; c.rel = r; c.reason = SatLit::positive(litVar);
    return c;
}

TEST_CASE("extractor: 2x + 3 >= 0 is linear with coeff 2 const 3") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId p = kernel->add(kernel->mul(two, x), three);  // 2x + 3

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Geq, 1) });
    REQUIRE(cc.linear.size() == 1);
    CHECK(cc.nonlinear.empty());
    const auto& la = cc.linear[0];
    REQUIRE(la.coeffs.size() == 1);
    CHECK(la.coeffs[0].first == kernel->getOrCreateVar("x"));
    CHECK(la.coeffs[0].second == mpq_class(2));
    CHECK(la.constant == mpq_class(3));
    CHECK(la.rel == Relation::Geq);
}

TEST_CASE("extractor: x*y - 1 is nonlinear") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId p = kernel->sub(kernel->mul(x, y), one);  // x*y - 1

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Eq, 1) });
    CHECK(cc.linear.empty());
    CHECK(cc.nonlinear.size() == 1);
}
