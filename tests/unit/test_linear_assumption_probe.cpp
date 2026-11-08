#include <doctest/doctest.h>
#include "search/linear/LinearAssumptionProbe.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <algorithm>
#include <stdexcept>

using namespace xolver;

namespace {
const LinearFormKey xForm{{{"x", 1}}}, yForm{{{"y", 1}}};
const LinearFormKey sumForm{{{"x", 1}, {"y", 1}}};
const LinearFormKey differenceForm{{{"x", 1}, {"y", -1}}};

bool holds(Relation relation, const mpq_class& left, const mpq_class& right) {
    switch (relation) {
        case Relation::Eq: return left == right;
        case Relation::Neq: return left != right;
        case Relation::Leq: return left <= right;
        case Relation::Lt: return left < right;
        case Relation::Geq: return left >= right;
        case Relation::Gt: return left > right;
    }
    throw std::logic_error("invalid test relation");
}

struct Context {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    int x = manager.getOrCreateVar(simplex, "x");
    int y = manager.getOrCreateVar(simplex, "y");

    void admit(const LinearFormKey& form, Relation relation, const mpq_class& rhs,
               SatLit reason, int level = 0) {
        const int auxiliary = manager.getOrCreateAuxVar(simplex, form, rhs);
        REQUIRE(manager.assertBound(simplex, auxiliary, relation, true, reason, level));
    }
};

struct AllocationOnly : SatSolver {
    SatVar next = 0;
    SatVar newVar() override { return ++next; }
    void addClause(const std::vector<SatLit>&) override {}
    SolveResult solve() override { throw std::logic_error("allocation only"); }
    SolveResult solve(const std::vector<SatLit>&) override { return solve(); }
    bool value(SatVar) const override { throw std::logic_error("allocation only"); }
    void setDeadline(std::chrono::steady_clock::time_point) override {}
};
}

TEST_CASE("Linear assumption probe: combined constraints refute an opposite bound without source mutation") {
    Context context;
    context.admit(sumForm, Relation::Leq, 2, SatLit::positive(1));
    context.admit(differenceForm, Relation::Leq, 0, SatLit::positive(2));
    REQUIRE(context.simplex.check() == GeneralSimplex::Result::Sat);
    const int variables = context.simplex.numVars();
    const auto analysis = context.simplex.analysisRevision(), point = context.simplex.pointRevision();
    const auto x = context.simplex.value(context.x), y = context.simplex.value(context.y);
    const std::vector<LinearProbeAssumption> assumptions{
        {xForm, Relation::Gt, 1, SatLit::negative(3)}};
    const auto result = probeLinearAssumptions(context.simplex, context.manager, assumptions);
    REQUIRE(result.status == GeneralSimplex::Result::Unsat);
    CHECK((result.conflictReasons == std::vector<SatLit>{
        SatLit::positive(1), SatLit::positive(2), SatLit::negative(3)}));
    CHECK_FALSE(result.model());
    CHECK(context.simplex.numVars() == variables);
    CHECK(context.simplex.analysisRevision() == analysis);
    CHECK(context.simplex.pointRevision() == point);
    CHECK(context.simplex.value(context.x) == x);
    CHECK(context.simplex.value(context.y) == y);
    CHECK_FALSE(context.simplex.hasImmediateConflict());
}

TEST_CASE("Linear assumption probe: every relation respects an exact equality pin") {
    for (const auto relation : {Relation::Eq, Relation::Neq, Relation::Lt,
                               Relation::Leq, Relation::Gt, Relation::Geq}) {
        for (int rhs = -1; rhs <= 1; ++rhs) {
            CAPTURE(relation);
            CAPTURE(rhs);
            Context context;
            context.admit(xForm, Relation::Eq, 0, SatLit::positive(1));
            const std::vector<LinearProbeAssumption> assumptions{
                {xForm, relation, mpq_class(rhs), SatLit::positive(2)}};
            const auto result = probeLinearAssumptions(context.simplex, context.manager, assumptions);
            const bool feasible = holds(relation, 0, rhs);
            REQUIRE(result.status == (feasible ? GeneralSimplex::Result::Sat : GeneralSimplex::Result::Unsat));
            if (feasible) {
                CHECK(result.conflictReasons.empty());
                const auto model = result.model();
                REQUIRE(model);
                CHECK(model->assignments.at("x") == DeltaRational(0));
                CHECK(model->delta > 0);
            } else {
                CHECK_FALSE(result.model());
                CHECK(std::find(result.conflictReasons.begin(), result.conflictReasons.end(),
                                SatLit::positive(2)) != result.conflictReasons.end());
            }
            if (relation == Relation::Neq && rhs == 0) CHECK(result.disequalityBranches == 2);
        }
    }
}

TEST_CASE("Linear assumption probe: disequality search restores failed alternatives") {
    Context context;
    context.admit(sumForm, Relation::Eq, 0, SatLit::positive(1));
    const std::vector<LinearProbeAssumption> separate{
        {xForm, Relation::Neq, 0, SatLit::positive(2)},
        {yForm, Relation::Neq, 0, SatLit::positive(3)}};
    const auto feasible = probeLinearAssumptions(context.simplex, context.manager, separate);
    REQUIRE(feasible.status == GeneralSimplex::Result::Sat);
    const auto model = feasible.model();
    REQUIRE(model);
    const auto x = model->assignments.at("x"), y = model->assignments.at("y");
    CHECK(x + y == DeltaRational(0));
    CHECK(x != DeltaRational(0));
    CHECK(y != DeltaRational(0));
    CHECK(feasible.disequalityBranches >= 3);
    auto impossible = separate;
    impossible.push_back({sumForm, Relation::Neq, 0, SatLit::positive(4)});
    const auto refuted = probeLinearAssumptions(context.simplex, context.manager, impossible);
    REQUIRE(refuted.status == GeneralSimplex::Result::Unsat);
    CHECK(std::find(refuted.conflictReasons.begin(), refuted.conflictReasons.end(),
                    SatLit::positive(4)) != refuted.conflictReasons.end());
    CHECK_FALSE(refuted.model());
    CHECK(context.simplex.check() == GeneralSimplex::Result::Sat);
}

TEST_CASE("Linear assumption probe: fresh symbols and large strict rationals stay isolated") {
    GeneralSimplex source;
    LinearAtomManager manager;
    mpz_class huge = 1;
    huge <<= 257;
    mpq_class lower(huge, mpz_class(7));
    lower.canonicalize();
    const mpq_class upper = lower + mpq_class(1, 5);
    const LinearFormKey fresh{{{"fresh", 1}}};
    const std::vector<LinearProbeAssumption> assumptions{
        {fresh, Relation::Gt, lower, SatLit::positive(1)},
        {fresh, Relation::Lt, upper, SatLit::positive(2)}};
    const auto result = probeLinearAssumptions(source, manager, assumptions);
    REQUIRE(result.status == GeneralSimplex::Result::Sat);
    const auto model = result.model();
    REQUIRE(model);
    const auto value = model->assignments.at("fresh");
    CHECK(value > DeltaRational(lower));
    CHECK(value < DeltaRational(upper));
    const mpq_class concrete = value.a + value.b * model->delta;
    CHECK(concrete > lower);
    CHECK(concrete < upper);
    CHECK(source.numVars() == 0);
    CHECK(manager.findVarIndex("fresh") == -1);
}

TEST_CASE("Linear assumption probe: source withdrawals and existing conflicts retain their contracts") {
    for (const auto policy : {GeneralSimplex::AssignmentPolicy::Preserve,
                              GeneralSimplex::AssignmentPolicy::Reinitialize}) {
        Context context;
        context.admit(xForm, Relation::Geq, 0, SatLit::positive(1));
        REQUIRE(context.simplex.check() == GeneralSimplex::Result::Sat);
        context.simplex.push();
        context.admit(xForm, Relation::Geq, 2, SatLit::positive(2), 1);
        const std::vector<LinearProbeAssumption> assumptions{
            {xForm, Relation::Leq, 1, SatLit::positive(3)}};
        CHECK(probeLinearAssumptions(context.simplex, context.manager, assumptions).status == GeneralSimplex::Result::Unsat);
        context.simplex.pop(policy);
        const auto point = context.simplex.pointRevision();
        const auto feasible = probeLinearAssumptions(context.simplex, context.manager, assumptions);
        CHECK(feasible.status == GeneralSimplex::Result::Sat);
        CHECK(context.simplex.pointRevision() == point);
        const int auxiliary = context.manager.getOrCreateAuxVar(context.simplex, xForm, 0);
        CHECK_FALSE(context.simplex.assertUpper(auxiliary,
            BoundInfo(BoundValue(DeltaRational(-1)), SatLit::positive(4))));
        for (int repeat = 0; repeat < 2; ++repeat) {
            const auto conflict = probeLinearAssumptions(context.simplex, context.manager, {});
            CHECK(conflict.status == GeneralSimplex::Result::Unsat);
            CHECK((conflict.conflictReasons == std::vector<SatLit>{SatLit::positive(1), SatLit::positive(4)}));
            CHECK(context.simplex.hasImmediateConflict());
        }
    }
}

TEST_CASE("Linear assumption probe: lazy witnesses own their state across source destruction and moves") {
    auto result = [] {
        Context context;
        context.admit(xForm, Relation::Eq, mpq_class(2, 3), SatLit::positive(1));
        return probeLinearAssumptions(context.simplex, context.manager, {});
    }();
    REQUIRE(result.status == GeneralSimplex::Result::Sat);
    auto moved = std::move(result);
    for (int repeat = 0; repeat < 2; ++repeat) {
        const auto model = moved.model();
        REQUIRE(model);
        CHECK(model->assignments.at("x") == DeltaRational(mpq_class(2, 3)));
        CHECK(model->delta > 0);
    }
}

TEST_CASE("Linear assumption probe: an expired caller deadline has no conclusion") {
    Context context;
    const std::vector<LinearProbeAssumption> assumptions{
        {xForm, Relation::Leq, 1, SatLit::positive(1)}};
    const auto result = probeLinearAssumptions(context.simplex, context.manager, assumptions,
        std::chrono::steady_clock::now() - std::chrono::milliseconds(1));
    CHECK(result.status == GeneralSimplex::Result::Unknown);
    CHECK(result.conflictReasons.empty());
    CHECK_FALSE(result.model());
    CHECK(result.simplexChecks == 0);
    auto invalid = assumptions;
    invalid.front().reason = SatLit{};
    CHECK_THROWS_AS(probeLinearAssumptions(context.simplex, context.manager, invalid), std::invalid_argument);
    invalid = assumptions;
    invalid.front().relation = static_cast<Relation>(255);
    CHECK_THROWS_AS(probeLinearAssumptions(context.simplex, context.manager, invalid), std::invalid_argument);
}

TEST_CASE("Linear assumption probe: retained contexts synchronize strengthening withdrawal and reasons") {
    Context context;
    context.admit(xForm, Relation::Geq, 0, SatLit::positive(1));
    LinearAssumptionProber prober;
    const std::vector<LinearProbeAssumption> negative{
        {xForm, Relation::Lt, 0, SatLit::positive(2)}};
    const auto first = prober.probe(context.simplex, context.manager, negative);
    REQUIRE(first.status == GeneralSimplex::Result::Unsat);
    CHECK(first.tableauCopies == 1);
    const auto repeat = prober.probe(context.simplex, context.manager, negative);
    CHECK(repeat.status == GeneralSimplex::Result::Unsat);
    CHECK(repeat.tableauCopies == 0);
    const int auxiliary = context.manager.getOrCreateAuxVar(context.simplex, xForm, 0);
    const DeltaRational zero(0);
    const std::vector<GeneralSimplex::ActiveBoundView> replacement{
        {auxiliary, true, &zero, SatLit::positive(17)}};
    REQUIRE(context.simplex.replaceActiveBoundViews(replacement));
    const auto changed = prober.probe(context.simplex, context.manager, negative);
    REQUIRE(changed.status == GeneralSimplex::Result::Unsat);
    CHECK(changed.tableauCopies == 0);
    CHECK((changed.conflictReasons == std::vector<SatLit>{SatLit::positive(2), SatLit::positive(17)}));
    for (const auto policy : {GeneralSimplex::AssignmentPolicy::Preserve,
                              GeneralSimplex::AssignmentPolicy::Reinitialize}) {
        context.simplex.push();
        context.admit(xForm, Relation::Geq, 2, SatLit::positive(3), 1);
        const std::vector<LinearProbeAssumption> belowOne{
            {xForm, Relation::Lt, 1, SatLit::positive(4)}};
        const auto child = prober.probe(context.simplex, context.manager, belowOne);
        REQUIRE(child.status == GeneralSimplex::Result::Unsat);
        CHECK(std::find(child.conflictReasons.begin(), child.conflictReasons.end(),
                        SatLit::positive(3)) != child.conflictReasons.end());
        context.simplex.pop(policy);
        const auto parent = prober.probe(context.simplex, context.manager, belowOne);
        REQUIRE(parent.status == GeneralSimplex::Result::Sat);
        const auto model = parent.model();
        REQUIRE(model);
        CHECK(model->assignments.at("x") >= DeltaRational(0));
        CHECK(model->assignments.at("x") < DeltaRational(1));
    }
    context.simplex.resetActiveBounds();
    const auto free = prober.probe(context.simplex, context.manager, negative);
    CHECK(free.status == GeneralSimplex::Result::Sat);
    CHECK(free.conflictReasons.empty());
}

TEST_CASE("Linear assumption probe: retained witnesses survive later queries and context reset") {
    Context context;
    LinearAssumptionProber prober;
    const std::vector<LinearProbeAssumption> one{{xForm, Relation::Eq, 1, SatLit::positive(1)}};
    const std::vector<LinearProbeAssumption> two{{xForm, Relation::Eq, 2, SatLit::positive(2)}};
    const auto first = prober.probe(context.simplex, context.manager, one);
    REQUIRE(first.status == GeneralSimplex::Result::Sat);
    REQUIRE(first.model());
    const auto second = prober.probe(context.simplex, context.manager, two);
    REQUIRE(second.status == GeneralSimplex::Result::Sat);
    CHECK(second.tableauCopies == 1);
    CHECK(first.model()->assignments.at("x") == DeltaRational(1));
    CHECK(second.model()->assignments.at("x") == DeltaRational(2));
    prober.reset();
    CHECK(first.model()->assignments.at("x") == DeltaRational(1));
    CHECK(second.model()->assignments.at("x") == DeltaRational(2));
    const auto expired = prober.probe(context.simplex, context.manager, one,
        std::chrono::steady_clock::now() - std::chrono::milliseconds(1));
    CHECK(expired.status == GeneralSimplex::Result::Unknown);
    CHECK(expired.tableauCopies == 0);
    CHECK_FALSE(expired.model());
    CHECK(prober.probe(context.simplex, context.manager, one).tableauCopies == 1);
}

TEST_CASE("Linear assumption probe: source growth replaces colliding query-only coordinates") {
    GeneralSimplex source;
    LinearAtomManager manager;
    manager.getOrCreateVar(source, "x");
    LinearAssumptionProber prober;
    const LinearFormKey fresh{{{"fresh", 1}}};
    const std::vector<LinearProbeAssumption> initial{{fresh, Relation::Eq, 3, SatLit::positive(1)}};
    CHECK(prober.probe(source, manager, initial).status == GeneralSimplex::Result::Sat);
    CHECK(source.numVars() == 1);
    const int auxiliary = manager.getOrCreateAuxVar(source, fresh, 7);
    REQUIRE(manager.assertBound(source, auxiliary, Relation::Eq, true, SatLit::positive(2)));
    const auto result = prober.probe(source, manager, initial);
    REQUIRE(result.status == GeneralSimplex::Result::Unsat);
    CHECK(result.tableauCopies == 1);
    CHECK((result.conflictReasons == std::vector<SatLit>{SatLit::positive(1), SatLit::positive(2)}));
    source.reset();
    manager = LinearAtomManager{};
    const auto unconstrained = prober.probe(source, manager, initial);
    REQUIRE(unconstrained.status == GeneralSimplex::Result::Sat);
    CHECK(unconstrained.tableauCopies == 1);
    REQUIRE(unconstrained.model());
    CHECK(unconstrained.model()->assignments.at("fresh") == DeltaRational(3));
}

TEST_CASE("Linear assumption probe: equation identities track definitions independently of bounds and pivots") {
    Context context;
    context.admit(sumForm, Relation::Eq, 2, SatLit::positive(1));
    const auto equations = context.simplex.definitionsIdentity();
    auto copied = context.simplex;
    CHECK(copied.definitionsIdentity() == equations);
    REQUIRE(context.simplex.assertLower(context.x,
        BoundInfo(BoundValue(DeltaRational(1)), SatLit::positive(2))));
    REQUIRE(context.simplex.check() == GeneralSimplex::Result::Sat);
    CHECK(context.simplex.definitionsIdentity() == equations);
    copied.addVar("independent");
    CHECK(copied.definitionsIdentity() != equations);
    CHECK(context.simplex.definitionsIdentity() == equations);
    Context other;
    other.admit(sumForm, Relation::Eq, 5, SatLit::positive(3));
    REQUIRE(other.simplex.numVars() == context.simplex.numVars());
    const auto replacement = other.simplex.definitionsIdentity();
    context.simplex = other.simplex;
    context.manager = other.manager;
    CHECK(context.simplex.definitionsIdentity() == replacement);
    CHECK(context.simplex.definitionsIdentity() != equations);
    LinearAssumptionProber prober;
    const std::vector<LinearProbeAssumption> wrong{{sumForm, Relation::Eq, 2, SatLit::positive(4)}};
    CHECK(prober.probe(context.simplex, context.manager, wrong).status == GeneralSimplex::Result::Unsat);
}

TEST_CASE("LraSolver: exact assumption projection combines rows using the existing vocabulary") {
    AllocationOnly allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator, nullptr);
    LraSolver solver;
    solver.setRegistry(&registry);
    auto atom = [&](const LinearFormKey& lhs, const mpq_class& rhs) {
        const auto variable = allocator.newVar();
        registry.registerParsedTheoryAtom(variable, NullExpr, TheoryId::LRA,
            LinearAtomPayload{lhs, Relation::Leq, RealValue::fromMpq(rhs)});
        return SatLit::positive(variable);
    };
    const auto first = atom(sumForm, 2), second = atom(differenceForm, 0), target = atom(xForm, 1);
    const auto count = registry.numAtomVars();
    for (const auto literal : {first, second})
        solver.assertLit(*registry.findBySatVar(literal.var), true, 1, literal);
    TheoryLemmaDatabase database;
    REQUIRE(solver.check(database).kind == TheoryCheckResult::Kind::Consistent);
    const auto lemmas = solver.takeEntailmentPropagations();
    REQUIRE(std::any_of(lemmas.begin(), lemmas.end(), [&](const auto& lemma) {
        return lemma.lits.back() == target;
    }));
    CHECK(registry.numAtomVars() == count);
    for (const auto& lemma : lemmas) {
        CHECK(lemma.kind == LemmaKind::Entailment);
        for (int xn = -8; xn <= 8; ++xn) for (int yn = -8; yn <= 8; ++yn) {
            mpq_class x(xn, 2), y(yn, 2);
            x.canonicalize();
            y.canonicalize();
            bool valid = false;
            for (const auto literal : lemma.lits) {
                const auto& payload = std::get<LinearAtomPayload>(registry.findBySatVar(literal.var)->payload);
                mpq_class lhs = 0;
                for (const auto& [name, coefficient] : payload.lhs.terms)
                    lhs += coefficient * (name == "x" ? x : y);
                valid |= holds(payload.rel, lhs, payload.rhs.asRational()) == literal.sign;
            }
            CHECK(valid);
        }
    }
    solver.backtrackToLevel(0);
    REQUIRE(solver.check(database).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(solver.takeEntailmentPropagations().empty());
    CHECK(registry.numAtomVars() == count);
}
