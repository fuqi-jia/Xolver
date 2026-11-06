#include <doctest/doctest.h>
#include "search/presolve/PresolveProjection.h"
#include "search/presolve/AffineSubstitution.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/arith/Reasoner.h"
#include "algebra/linear/LinearExpr.h"
#include <stdexcept>

using namespace xolver;

namespace {
RationalPolynomial variable(VarId id) { return RationalPolynomial::fromVar(id, 1, 1); }
RationalPolynomial constant(const mpq_class& value) { return RationalPolynomial::fromConstant(value); }
class RealProjectionProbe : public NraSolver {
public:
    using NraSolver::NraSolver;
    std::optional<TheoryCheckResult> stage(const std::string& name, TheoryLemmaStorage& db) {
        for (auto& reasoner : reasoners_)
            if (reasoner->name() == name) return reasoner->run(db, TheoryEffort::Full);
        throw std::logic_error("missing real projection stage");
    }
};
class IntegerProjectionProbe : public NiaSolver {
public:
    using NiaSolver::NiaSolver;
    std::optional<TheoryCheckResult> stage(const std::string& name, TheoryLemmaStorage& db) {
        for (auto& reasoner : reasoners_)
            if (reasoner->name() == name) return reasoner->run(db, TheoryEffort::Full);
        throw std::logic_error("missing integer projection stage");
    }
};

template<class Solver>
void checkProjectedRefutation(TheoryId theory, const std::string& prefix) {
    auto owned = createPolynomialKernel();
    auto& kernel = *owned;
    std::vector<PolyId> aliases;
    for (unsigned i = 0; i < 132; ++i)
        aliases.push_back(kernel.mkVar(kernel.getOrCreateVar("a" + std::to_string(i))));
    const auto x = kernel.mkVar(kernel.getOrCreateVar("x"));
    const auto y = kernel.mkVar(kernel.getOrCreateVar("y"));
    Solver solver(std::move(owned));
    std::vector<SatLit> sources;
    const auto add = [&](PolyId poly, Relation relation) {
        const auto id = static_cast<SatVar>(sources.size() + 1);
        const bool value = id % 2 == 0;
        const auto literal = SatLit{id, value};
        const auto atomRelation = value ? relation : negateRelation(relation);
        TheoryAtomRecord atom{id, theory, false, NullExpr,
            PolynomialAtomPayload{poly, atomRelation, RealValue::fromInt(0)}};
        solver.assertLit(atom, value, 1, literal);
        sources.push_back(literal);
    };
    for (unsigned i = 0; i < aliases.size(); ++i)
        add(kernel.sub(aliases[i], kernel.add(kernel.add(x,y), kernel.mkConst(i))), Relation::Eq);
    const auto quadratic = kernel.sub(
        kernel.add(kernel.pow(aliases[0],2), kernel.add(kernel.pow(x,2),kernel.pow(y,2))),
        kernel.mul(kernel.mkConst(3),kernel.mul(x,y)));
    add(quadratic, Relation::Lt);
    TheoryLemmaDatabase db;
    if (theory == TheoryId::NIA) REQUIRE_FALSE(solver.stage("nia.normalize", db));
    REQUIRE_FALSE(solver.stage(prefix + ".presolve", db));
    const auto result = solver.stage(prefix + ".sign-refute", db);
    CHECK(result.has_value());
    if (!result) return;
    REQUIRE(result->kind == TheoryCheckResult::Kind::Conflict);
    REQUIRE(result->conflictOpt);
    const auto& clause = result->conflictOpt->clause;
    CHECK(clause.size() == 2);
    for (const auto required : {sources.front(), sources.back()})
        CHECK(std::find(clause.begin(), clause.end(), required) != clause.end());
    for (const auto source : clause)
        CHECK(std::find(sources.begin(), sources.end(), source) != sources.end());
    solver.backtrackToLevel(0);
    if (theory == TheoryId::NIA) REQUIRE_FALSE(solver.stage("nia.normalize", db));
    CHECK_FALSE(solver.stage(prefix + ".sign-refute", db));
}
}

TEST_CASE("Projected refutation: eliminated equations remain guards of exact integer and real conflicts") {
    checkProjectedRefutation<IntegerProjectionProbe>(TheoryId::NIA, "nia");
    checkProjectedRefutation<RealProjectionProbe>(TheoryId::NRA, "nra");
}

TEST_CASE("Presolve handoff: definition reconstruction is exact and transactional") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    PolynomialDefinitions definitions{{0, y + constant(mpq_class(1,3))},
                                      {1, z * constant(-2)}};
    WorkBudget work(0);
    std::unordered_map<VarId, mpq_class> model{{2, mpq_class(5,7)}};
    REQUIRE(reconstructPolynomialDefinitions(definitions, model, work));
    CHECK(model.at(1) == mpq_class(-10,7));
    CHECK(model.at(0) == mpq_class(-23,21));
    CHECK(reconstructPolynomialDefinitions(definitions, model, work));
    model[0] = 0;
    const auto wrong = model;
    CHECK_FALSE(reconstructPolynomialDefinitions(definitions, model, work));
    CHECK(model == wrong);
    model.clear();
    CHECK_FALSE(reconstructPolynomialDefinitions(definitions, model, work));
    CHECK(model.empty());
    const PolynomialDefinitions cycle{{0, y}, {1, x}};
    CHECK_FALSE(reconstructPolynomialDefinitions(cycle, model, work));
    CHECK(model.empty());
    WorkBudget exhausted(1);
    CHECK_THROWS_AS(reconstructPolynomialDefinitions(definitions, model, exhausted), ResourceExhausted);
    CHECK(model.empty());
}

TEST_CASE("Presolve handoff: real and integer projections retain all signed source premises") {
    for (bool integer : {false, true}) {
        auto kernel = createPolynomialKernel();
        const auto ix = kernel->getOrCreateVar("x"), iy = kernel->getOrCreateVar("y");
        const auto iz = kernel->getOrCreateVar("z");
        const auto x = variable(ix), y = variable(iy), z = variable(iz);
        const mpq_class coefficient = integer ? mpq_class(2) : mpq_class(2,3);
        const auto definition = x - y * constant(coefficient) - constant(1);
        const auto residual = x * z - constant(3);
        PresolveState state;
        state.kernel = kernel.get(); state.integerDomain = integer;
        state.atoms = {{definition, Relation::Eq, {{SatLit::negative(11)}, {}}},
                       {residual, Relation::Geq, {{SatLit::positive(47)}, {}}}};
        AffineSubstitution affine;
        REQUIRE(affine.run(state));
        WorkBudget work(0);
        const auto projection = PresolveProjection::build(state, work);
        REQUIRE(projection);
        REQUIRE(projection->constraints().size() == 1);
        CHECK(projection->definitionCount() == 1);
        CHECK((projection->premises() == std::vector<SatLit>{SatLit::negative(11), SatLit::positive(47)}));
        CHECK(projection->constraints().front().premises.size() == 2);
        for (int a = -3; a <= 3; ++a) for (int b = -3; b <= 3; ++b) {
            std::unordered_map<VarId, mpq_class> point{{iy, a}, {iz, b}};
            REQUIRE(projection->reconstruct(point, work));
            CHECK(definition.evaluateRational(point) == 0);
            CHECK(point.at(ix) == coefficient * a + 1);
            std::unordered_map<std::string, mpq_class> named;
            for (const auto& [id, value] : point) named.emplace(kernel->varName(id), value);
            const auto reducedSign = kernel->sgn(projection->constraints().front().poly, named);
            const auto exact = residual.evaluateRational(point);
            CHECK((reducedSign < 0) == (exact < 0));
            CHECK((reducedSign > 0) == (exact > 0));
        }
        std::unordered_map<VarId, mpq_class> incomplete{{iy, 1}};
        const auto before = incomplete;
        CHECK_FALSE(projection->reconstruct(incomplete, work));
        CHECK(incomplete == before);
        state = PresolveState{};
        CHECK(projection->premises().size() == 2);
        CHECK_FALSE(PresolveProjection::build(state, work));
    }
}

TEST_CASE("Presolve handoff: unused free coordinates and integer sort checks remain explicit") {
    auto kernel = createPolynomialKernel();
    const auto ix = kernel->getOrCreateVar("x"), iy = kernel->getOrCreateVar("y");
    PresolveState state;
    state.kernel = kernel.get(); state.integerDomain = true;
    state.atoms = {{variable(ix) - variable(iy), Relation::Eq, {{SatLit::positive(3)}, {}}}};
    AffineSubstitution affine;
    REQUIRE(affine.run(state));
    WorkBudget work(0);
    const auto projection = PresolveProjection::build(state, work);
    REQUIRE(projection);
    CHECK(projection->constraints().empty());
    std::unordered_map<VarId, mpq_class> point;
    REQUIRE(projection->reconstruct(point, work));
    CHECK(point.at(ix) == 0);
    CHECK(point.at(iy) == 0);
    point = {{iy, mpq_class(1,2)}};
    const auto fractional = point;
    CHECK_FALSE(projection->reconstruct(point, work));
    CHECK(point == fractional);
    state.hasConflict = true;
    CHECK_FALSE(PresolveProjection::build(state, work));
}

TEST_CASE("Presolve handoff: real candidate search reconstructs exact original values") {
    auto owned = createPolynomialKernel();
    auto& kernel = *owned;
    const auto ix = kernel.getOrCreateVar("x"), iy = kernel.getOrCreateVar("y");
    const auto iz = kernel.getOrCreateVar("z");
    const auto x = kernel.mkVar(ix), y = kernel.mkVar(iy), z = kernel.mkVar(iz);
    RealProjectionProbe solver(std::move(owned));
    const auto definition = kernel.sub(kernel.mul(kernel.mkConst(7), x),
                                     kernel.mul(kernel.mkConst(3), y));
    const auto product = kernel.sub(kernel.mul(y,z), kernel.mkOne());
    for (const auto& [poly, id] : std::vector<std::pair<PolyId, SatVar>>{{definition, 1}, {product, 2}}) {
        TheoryAtomRecord atom{id, TheoryId::NRA, false, NullExpr,
            PolynomialAtomPayload{poly, Relation::Eq, RealValue::fromInt(0)}};
        solver.assertLit(atom, true, 1, SatLit::positive(id));
    }
    TheoryLemmaDatabase db;
    REQUIRE_FALSE(solver.stage("nra.presolve", db));
    const auto result = solver.stage("nra.partial-linear-model", db);
    REQUIRE(result);
    CHECK(result->kind == TheoryCheckResult::Kind::Consistent);
    const auto model = solver.getModel();
    REQUIRE(model);
    const auto qx = model->numericAssignments.at("x").tryAsRational();
    const auto qy = model->numericAssignments.at("y").tryAsRational();
    const auto qz = model->numericAssignments.at("z").tryAsRational();
    REQUIRE(qx); REQUIRE(qy); REQUIRE(qz);
    CHECK(7 * *qx == 3 * *qy);
    CHECK(*qy * *qz == 1);
    solver.backtrackToLevel(0);
    CHECK_FALSE(solver.getModel());
}
