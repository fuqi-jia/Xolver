#include <doctest/doctest.h>
#include "search/refute/PolynomialProductSplit.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "algebra/poly/RationalPolynomial.h"
#include "contracts/DynamicAtomRegistrar.h"
#include "search/coordination/TheoryManager.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "search/arith/Reasoner.h"

using namespace xolver;

namespace {
struct ProductRegistrar : DynamicAtomRegistrar {
    SatSolver& solver;
    explicit ProductRegistrar(SatSolver& sat) : solver(sat) {}
    SatLit registerDynamicAtom(ExprId, TheoryId) override { return SatLit::positive(solver.newVar()); }
};
struct ProductFixture {
    std::unique_ptr<SatSolver> sat = createSatSolver();
    ProductRegistrar registrar{*sat};
    TheoryAtomRegistry registry;
    TheoryManager theories;
    TheoryLemmaDatabase db;
    CadicalBackend& backend = dynamic_cast<CadicalBackend&>(*sat);
    CadicalTheoryPropagator propagator{registry, theories, db, backend};
    ProductFixture() {
        registry.setContext(sat.get(), &registrar);
        backend.connectPropagator(&propagator);
    }
    ~ProductFixture() { backend.disconnectPropagator(); }
};
struct RealProductProbe : NraSolver {
    using NraSolver::NraSolver;
    std::optional<TheoryCheckResult> signCheck(TheoryLemmaStorage& db, TheoryEffort effort) {
        for (auto& stage : reasoners_)
            if (stage->name() == "nra.sign-refute") return stage->run(db, effort);
        return std::nullopt;
    }
};
}

TEST_CASE("Shared product split: exact integer and rational covers include every zero factor") {
    for (const auto theory : {TheoryId::NIA, TheoryId::NRA}) {
        auto kernel = createPolynomialKernel();
        const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
        const auto z = kernel->getOrCreateVar("z");
        ProductFixture fixture;
        auto& sat = fixture.sat;
        auto& registry = fixture.registry;
        auto& db = fixture.db;
        const auto premise = SatLit::negative(sat->newVar());
        const auto residual = kernel->sub(kernel->mkVar(y), kernel->mkVar(z));
        const auto polynomial = kernel->mul(kernel->mkConst(-7), kernel->mul(
            kernel->mul(kernel->pow(kernel->mkVar(x), 2), kernel->pow(kernel->mkVar(y), 3)), residual));
        const auto lemma = splitZeroPolynomialProduct(polynomial, premise, *kernel, theory, registry, db);
        REQUIRE(lemma);
        REQUIRE(lemma->lits.size() == 4);
        const auto original = RationalPolynomial::fromPolyId(polynomial, *kernel);
        REQUIRE(original);
        for (int a = -2; a <= 2; ++a) for (int b = -2; b <= 2; ++b) for (int c = -2; c <= 2; ++c) {
            const mpq_class denominator(theory == TheoryId::NIA ? 1 : 3);
            const std::unordered_map<VarId, mpq_class> point{{x, mpq_class(a)/denominator},
                {y, mpq_class(b)/denominator}, {z, mpq_class(c)/denominator}};
            bool cover = false;
            for (const auto literal : lemma->lits) {
                if (literal == premise.negated()) continue;
                const auto* atom = registry.findBySatVar(literal.var);
                REQUIRE(atom);
                CHECK(atom->theory == theory);
                const auto* payload = std::get_if<PolynomialAtomPayload>(&atom->payload);
                REQUIRE(payload);
                CHECK(payload->rel == Relation::Eq);
                const auto factor = RationalPolynomial::fromPolyId(payload->poly, *kernel);
                REQUIRE(factor);
                cover |= factor->evaluateRational(point) == payload->rhs.asRational();
            }
            CHECK(cover == (original->evaluateRational(point) == 0));
        }
        db.markInstalled(*lemma);
        CHECK_FALSE(splitZeroPolynomialProduct(polynomial, premise, *kernel, theory, registry, db));
    }
}

TEST_CASE("Shared product split: constants irreducible sums and large powers retain exact semantics") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    ProductFixture fixture;
    auto& sat = fixture.sat;
    auto& registry = fixture.registry;
    auto& db = fixture.db;
    const auto premise = SatLit::positive(sat->newVar());
    for (const auto polynomial : {kernel->mkZero(), kernel->mkOne(), kernel->add(x, y),
            kernel->add(kernel->mul(x, y), kernel->mkOne())})
        CHECK_FALSE(splitZeroPolynomialProduct(polynomial, premise, *kernel, TheoryId::NIA, registry, db));
    CHECK(registry.numAtomVars() == 0);
    const auto lemma = splitZeroPolynomialProduct(kernel->pow(x, 10000), premise,
        *kernel, TheoryId::NIA, registry, db);
    REQUIRE(lemma);
    CHECK(lemma->lits.size() == 2);
    CHECK(registry.numAtomVars() == 1);
}

TEST_CASE("Shared product split: real theory publishes full covers and withdraws their premises") {
    ProductFixture f;
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto product = kernel->mul(x, y);
    RealProductProbe solver(std::move(kernel));
    solver.setRegistry(&f.registry);
    const auto reason = SatLit::positive(f.sat->newVar());
    TheoryAtomRecord atom{reason.var, TheoryId::NRA, false, NullExpr,
        PolynomialAtomPayload{product, Relation::Eq, RealValue::fromInt(0)}};
    solver.assertLit(atom, true, 1, reason);
    CHECK_FALSE(solver.signCheck(f.db, TheoryEffort::Standard));
    CHECK(f.registry.numAtomVars() == 0);
    const auto result = solver.signCheck(f.db, TheoryEffort::Full);
    REQUIRE(result);
    REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
    REQUIRE(result->lemmaOpt);
    CHECK(result->lemmaOpt->lits.size() == 3);
    f.db.markInstalled(*result->lemmaOpt);
    solver.backtrackToLevel(0);
    CHECK_FALSE(solver.signCheck(f.db, TheoryEffort::Full));
}
