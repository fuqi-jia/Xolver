#include <doctest/doctest.h>
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/proof/CellCertificateValidator.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace xolver;

static CdcacInput makeUnivariateInput(PolynomialKernel* kernel, PolyId poly, Relation rel, SatLit reason) {
    CdcacInput input;
    CdcacConstraint c;
    c.poly = poly;
    c.rel = rel;
    c.reason = reason;
    input.constraints.push_back(c);
    VarId var = kernel->getOrCreateVar("x");
    input.varOrder.push_back(var);
    return input;
}

TEST_CASE("V3 certificate: univariate x^2 = 1 -> SAT") {
    auto kernel = createPolynomialKernel();
    auto backend = std::make_unique<LibpolyBackend>(kernel.get());
    CdcacCore core(kernel.get(), backend.get());

    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);
    PolyId x2 = kernel->pow(xPoly, 2);  // x^2
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId x2_minus_1 = kernel->sub(x2, one);  // x^2 - 1

    auto input = makeUnivariateInput(kernel.get(), x2_minus_1, Relation::Eq, SatLit::positive(1));
    auto result = core.solve(input);

    // x^2 - 1 = 0 has real roots x = ±1, so this is SAT
    CHECK(result.status == CdcacStatus::Sat);
}

TEST_CASE("V3 certificate: univariate x^2 < 0 -> UNSAT with coveringCert") {
    auto kernel = createPolynomialKernel();
    auto backend = std::make_unique<LibpolyBackend>(kernel.get());
    CdcacCore core(kernel.get(), backend.get());

    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);
    PolyId x2 = kernel->pow(xPoly, 2);  // x^2

    auto input = makeUnivariateInput(kernel.get(), x2, Relation::Lt, SatLit::positive(1));
    auto result = core.solve(input);

    CHECK(result.status == CdcacStatus::Unsat);
    REQUIRE(result.coveringCert.has_value());
    CHECK(!result.coveringCert->cells.empty());

    // Every cell certificate must have non-empty atomConditions
    for (const auto& cc : result.coveringCert->cells) {
        CHECK(!cc.certificate.atomConditions.empty());
    }

    // Validate the covering certificate
    CellCertificateValidator validator;
    auto valRes = validator.validateCovering(*result.coveringCert, backend.get());
    CHECK(valRes.status == ValidationStatus::Valid);
}

TEST_CASE("V3 certificate: univariate x^2 > 0 AND x^2 < 0 -> UNSAT with validator pass") {
    auto kernel = createPolynomialKernel();
    auto backend = std::make_unique<LibpolyBackend>(kernel.get());
    CdcacCore core(kernel.get(), backend.get());

    VarId x = kernel->getOrCreateVar("x");
    PolyId xPoly = kernel->mkVar(x);
    PolyId x2 = kernel->pow(xPoly, 2);  // x^2

    CdcacInput input;
    CdcacConstraint c1;
    c1.poly = x2;
    c1.rel = Relation::Gt;
    c1.reason = SatLit::positive(1);
    input.constraints.push_back(c1);

    CdcacConstraint c2;
    c2.poly = x2;
    c2.rel = Relation::Lt;
    c2.reason = SatLit::positive(2);
    input.constraints.push_back(c2);

    input.varOrder.push_back(x);

    auto result = core.solve(input);

    // x^2 > 0 AND x^2 < 0 is UNSAT (contradiction)
    CHECK(result.status == CdcacStatus::Unsat);
    REQUIRE(result.coveringCert.has_value());
    CHECK(!result.coveringCert->cells.empty());

    // Validate the covering certificate
    CellCertificateValidator validator;
    auto valRes = validator.validateCovering(*result.coveringCert, backend.get());
    CHECK(valRes.status == ValidationStatus::Valid);
}

TEST_CASE("V3 certificate: bivariate x*y = 0, x > 0, y > 0 -> UNSAT") {
    auto kernel = createPolynomialKernel();
    auto backend = std::make_unique<LibpolyBackend>(kernel.get());
    CdcacCore core(kernel.get(), backend.get());

    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");
    PolyId xPoly = kernel->mkVar(x);
    PolyId yPoly = kernel->mkVar(y);
    PolyId xy = kernel->mul(xPoly, yPoly);  // x*y

    CdcacInput input;

    CdcacConstraint c1;
    c1.poly = xy;
    c1.rel = Relation::Eq;
    c1.reason = SatLit::positive(1);
    input.constraints.push_back(c1);

    CdcacConstraint c2;
    c2.poly = x;
    c2.rel = Relation::Gt;
    c2.reason = SatLit::positive(2);
    input.constraints.push_back(c2);

    CdcacConstraint c3;
    c3.poly = y;
    c3.rel = Relation::Gt;
    c3.reason = SatLit::positive(3);
    input.constraints.push_back(c3);

    input.varOrder.push_back(x);
    input.varOrder.push_back(y);

    auto result = core.solve(input);

    // This should be UNSAT: x*y = 0, x > 0, y > 0 implies x=0 or y=0, contradicting x>0 and y>0
    CHECK(result.status == CdcacStatus::Unsat);
    REQUIRE(result.coveringCert.has_value());
    CHECK(!result.coveringCert->cells.empty());

    // Validate the covering certificate
    CellCertificateValidator validator;
    auto valRes = validator.validateCovering(*result.coveringCert, backend.get());
    CHECK(valRes.status == ValidationStatus::Valid);
}
