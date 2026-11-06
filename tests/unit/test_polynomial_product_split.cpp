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
#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "base/SolveClock.h"
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
    std::optional<TheoryCheckResult> run(const std::string& name, TheoryLemmaStorage& db, TheoryEffort effort) {
        for (auto& stage : reasoners_)
            if (stage->name() == name)
                return stage->runsAt(effort) ? stage->run(db, effort) : std::nullopt;
        return std::nullopt;
    }
};
struct IntegerProductProbe : NiaSolver {
    using NiaSolver::NiaSolver;
    std::optional<TheoryCheckResult> run(const std::string& name, TheoryLemmaStorage& db, TheoryEffort effort) {
        for (auto& stage : reasoners_)
            if (stage->name() == name)
                return stage->runsAt(effort) ? stage->run(db, effort) : std::nullopt;
        return std::nullopt;
    }
};
}

TEST_CASE("Shared sign partition: integer and real covers retain the zero boundary") {
    for (const auto theory : {TheoryId::NIA, TheoryId::NRA}) {
        auto kernel = createPolynomialKernel();
        const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
        const auto xp = kernel->mkVar(x), yp = kernel->mkVar(y);
        ProductFixture f;
        auto constraint = [&](PolyId poly, Relation relation) {
            return SignRefuteConstraint{*RationalPolynomial::fromPolyId(poly, *kernel), relation,
                SatLit::positive(f.sat->newVar())};
        };
        const std::vector<SignRefuteConstraint> context{
            constraint(kernel->mul(xp, yp), Relation::Geq),
            constraint(kernel->mul(kernel->mkConst(-2), xp), Relation::Leq),
            constraint(yp, Relation::Gt)};
        const auto lemma = splitNonlinearVariableSigns(context, *kernel, theory, f.registry, f.db);
        REQUIRE(lemma);
        CHECK(lemma->kind == LemmaKind::Entailment);
        REQUIRE(lemma->lits.size() == 3);
        for (int value = -5; value <= 5; ++value) {
            const mpq_class point(value, theory == TheoryId::NIA ? 1 : 3);
            int alternatives = 0;
            for (const auto literal : lemma->lits) {
                const auto* atom = f.registry.findBySatVar(literal.var);
                REQUIRE(atom);
                CHECK(atom->theory == theory);
                const auto* payload = std::get_if<PolynomialAtomPayload>(&atom->payload);
                REQUIRE(payload);
                CHECK(payload->poly == xp);
                CHECK(payload->rhs.asRational() == 0);
                const bool holds = payload->rel == Relation::Lt ? point < 0 :
                    payload->rel == Relation::Eq ? point == 0 : point > 0;
                alternatives += holds == literal.sign;
            }
            CHECK(alternatives == 1);
        }
        const auto variables = f.registry.numAtomVars();
        // An undelivered partition can be retried. Installation, rather than
        // mere construction, decides whether later stages may proceed.
        const auto retry = splitNonlinearVariableSigns(context, *kernel, theory, f.registry, f.db);
        REQUIRE(retry);
        CHECK(retry->lits == lemma->lits);
        f.db.markInstalled(*lemma);
        CHECK_FALSE(splitNonlinearVariableSigns(context, *kernel, theory, f.registry, f.db));
        CHECK(f.registry.numAtomVars() == variables);
    }
}

TEST_CASE("Shared sign partition: exact bound signs and cancellation avoid useless predicates") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
    const auto xp = kernel->mkVar(x), yp = kernel->mkVar(y);
    auto rp = [&](PolyId poly) { return *RationalPolynomial::fromPolyId(poly, *kernel); };
    const auto product = rp(kernel->mul(xp, yp));
    const auto negative = rp(kernel->neg(xp));
    const auto shifted = rp(kernel->sub(kernel->mul(kernel->mkConst(2), xp), kernel->mkOne()));
    for (const auto& [polynomial, relation] : std::vector<std::pair<RationalPolynomial, Relation>>{
            {rp(xp), Relation::Eq}, {rp(xp), Relation::Gt}, {rp(xp), Relation::Lt},
            {negative, Relation::Gt}, {negative, Relation::Lt}, {shifted, Relation::Geq}}) {
        ProductFixture f;
        const std::vector<SignRefuteConstraint> context{
            {product, Relation::Geq, SatLit::positive(f.sat->newVar())},
            {polynomial, relation, SatLit::positive(f.sat->newVar())},
            {rp(yp), Relation::Gt, SatLit::positive(f.sat->newVar())}};
        CHECK_FALSE(splitNonlinearVariableSigns(context, *kernel, TheoryId::NRA, f.registry, f.db));
        CHECK(f.registry.numAtomVars() == 0);
    }
    ProductFixture f;
    const std::vector<SignRefuteConstraint> even{
        {rp(kernel->add(kernel->pow(xp, 2), kernel->pow(yp, 4))), Relation::Geq,
            SatLit::positive(f.sat->newVar())}};
    CHECK_FALSE(splitNonlinearVariableSigns(even, *kernel, TheoryId::NIA, f.registry, f.db));
    const std::vector<SignRefuteConstraint> unresolved{
        {product, Relation::Geq, SatLit::positive(f.sat->newVar())}};
    wall::endSolve();
    {
        wall::DeadlineScope deadline(std::chrono::steady_clock::now() - std::chrono::seconds(1));
        CHECK_FALSE(splitNonlinearVariableSigns(unresolved, *kernel, TheoryId::NIA, f.registry, f.db));
        CHECK(f.registry.numAtomVars() == 0);
    }
    CHECK(splitNonlinearVariableSigns(unresolved, *kernel, TheoryId::NIA, f.registry, f.db));
}

TEST_CASE("Shared sign partition: both theory pipelines deliver only at full effort") {
    for (const auto theory : {TheoryId::NIA, TheoryId::NRA}) {
        ProductFixture f;
        auto kernel = createPolynomialKernel();
        const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
        const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
        const auto product = kernel->mul(x, y);
        std::unique_ptr<ArithSolverBase> solver;
        const std::string stage = theory == TheoryId::NIA ? "nia.sign-partition" : "nra.sign-partition";
        auto run = [&](TheoryEffort effort) {
            if (theory == TheoryId::NIA)
                return static_cast<IntegerProductProbe&>(*solver).run(stage, f.db, effort);
            return static_cast<RealProductProbe&>(*solver).run(stage, f.db, effort);
        };
        if (theory == TheoryId::NIA) {
            auto instance = std::make_unique<IntegerProductProbe>(std::move(kernel));
            instance->setRegistry(&f.registry);
            solver = std::move(instance);
        } else {
            auto instance = std::make_unique<RealProductProbe>(std::move(kernel));
            instance->setRegistry(&f.registry);
            solver = std::move(instance);
        }
        auto add = [&](PolyId poly, Relation relation) {
            const auto reason = SatLit::positive(f.sat->newVar());
            const TheoryAtomRecord atom{reason.var, theory, false, NullExpr,
                PolynomialAtomPayload{poly, relation, RealValue::fromInt(0)}};
            solver->assertLit(atom, true, 1, reason);
        };
        add(product, Relation::Geq);
        add(x, Relation::Geq);
        add(y, Relation::Gt);
        CHECK_FALSE(run(TheoryEffort::Standard));
        CHECK(f.registry.numAtomVars() == 0);
        const auto result = run(TheoryEffort::Full);
        REQUIRE(result);
        REQUIRE(result->lemmaOpt);
        CHECK(result->lemmaOpt->lits.size() == 3);
        f.db.markInstalled(*result->lemmaOpt);
        CHECK_FALSE(run(TheoryEffort::Full));
        solver->backtrackToLevel(0);
        CHECK_FALSE(run(TheoryEffort::Full));
    }
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
        const auto lemma = splitZeroPolynomialProduct(polynomial, {premise}, *kernel, theory, registry, db);
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
        CHECK_FALSE(splitZeroPolynomialProduct(polynomial, {premise}, *kernel, theory, registry, db));
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
        CHECK_FALSE(splitZeroPolynomialProduct(polynomial, {premise}, *kernel, TheoryId::NIA, registry, db));
    CHECK(registry.numAtomVars() == 0);
    const auto lemma = splitZeroPolynomialProduct(kernel->pow(x, 10000), {premise},
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
    CHECK_FALSE(solver.run("nra.sign-refute", f.db, TheoryEffort::Standard));
    CHECK(f.registry.numAtomVars() == 0);
    const auto result = solver.run("nra.sign-refute", f.db, TheoryEffort::Full);
    REQUIRE(result);
    REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
    REQUIRE(result->lemmaOpt);
    CHECK(result->lemmaOpt->lits.size() == 3);
    f.db.markInstalled(*result->lemmaOpt);
    solver.backtrackToLevel(0);
    CHECK_FALSE(solver.run("nra.sign-refute", f.db, TheoryEffort::Full));
}

TEST_CASE("Proved product feedback: covers retain every signed proof premise") {
    ProductFixture f;
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto product = kernel->mul(x, y);
    const std::vector<SatLit> premises{SatLit::positive(f.sat->newVar()),
        SatLit::negative(f.sat->newVar())};
    CHECK_FALSE(splitZeroPolynomialProduct(product, {}, *kernel, TheoryId::NIA, f.registry, f.db));
    CHECK(f.registry.numAtomVars() == 0);
    const auto lemma = splitZeroPolynomialProduct(product, premises, *kernel,
        TheoryId::NIA, f.registry, f.db);
    REQUIRE(lemma);
    REQUIRE(lemma->lits.size() == 4);
    for (const auto premise : premises)
        CHECK(std::find(lemma->lits.begin(), lemma->lits.end(), premise.negated()) != lemma->lits.end());
}

TEST_CASE("Proved product feedback: real relaxation publishes its coupled zero proof only at full effort") {
    ProductFixture f;
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const auto w = kernel->mkVar(kernel->getOrCreateVar("w"));
    const auto t = kernel->mkVar(kernel->getOrCreateVar("t"));
    const auto sum = kernel->add(kernel->mul(x, y), z);
    const auto outside = kernel->mul(w, t);
    RealProductProbe solver(std::move(kernel));
    solver.setRegistry(&f.registry);
    const auto add = [&](PolyId poly, Relation relation, int rhs) {
        const auto reason = SatLit::positive(f.sat->newVar());
        TheoryAtomRecord atom{reason.var, TheoryId::NRA, false, NullExpr,
            PolynomialAtomPayload{poly, relation, RealValue::fromInt(rhs)}};
        solver.assertLit(atom, true, 1, reason);
    };
    for (const auto variable : {x, y, z, w, t}) add(variable, Relation::Geq, 0);
    add(sum, Relation::Leq, 0);
    add(outside, Relation::Eq, 1);
    CHECK_FALSE(solver.run("nra.linear-relaxation", f.db, TheoryEffort::Standard));
    CHECK(f.registry.numAtomVars() == 0);
    const auto result = solver.run("nra.linear-relaxation", f.db, TheoryEffort::Full);
    REQUIRE(result);
    REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
    REQUIRE(result->lemmaOpt);
    CHECK(result->lemmaOpt->lits.size() > 3);
    CHECK(f.registry.numAtomVars() == 2);
}
