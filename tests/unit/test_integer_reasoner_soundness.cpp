#include <doctest/doctest.h>
#include "search/linear/IntegerReasoner.h"
#include "search/linear/BoundAxiomGenerator.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <algorithm>
#include <stdexcept>
#include <unordered_map>

using namespace xolver;
namespace {
using Values = std::unordered_map<std::string, mpq_class>;
bool compare(Relation r, const mpq_class& a, const mpq_class& b) {
    switch (r) {
        case Relation::Eq: return a == b;
        case Relation::Neq: return a != b;
        case Relation::Leq: return a <= b;
        case Relation::Geq: return a >= b;
        case Relation::Lt: return a < b;
        case Relation::Gt: return a > b;
    }
    throw std::logic_error("invalid relation");
}


mpq_class eval(const LinearFormKey& form, const Values& values) {
    mpq_class result = 0;
    for (const auto& [name, coefficient] : form.terms)
        result += coefficient * values.at(name);
    return result;
}
struct Allocator : SatSolver, DynamicAtomRegistrar {
    SatVar next = 0;
    SatVar newVar() override { return ++next; }
    void addClause(const std::vector<SatLit>&) override {}
    SolveResult solve() override { throw std::logic_error("allocation only"); }
    SolveResult solve(const std::vector<SatLit>&) override { return solve(); }
    bool value(SatVar) const override { throw std::logic_error("allocation only"); }
    void setDeadline(std::chrono::steady_clock::time_point) override {}
    SatLit registerDynamicAtom(ExprId, TheoryId) override { return SatLit::positive(newVar()); }
};
struct Fixture {
    Allocator allocator;
    TheoryAtomRegistry registry;
    IntegerReasoner reasoner;
    Fixture() {
        registry.setContext(&allocator, &allocator);
        reasoner.setRegistry(&registry);
    }
    ActiveLinearAtom atom(LinearFormKey lhs, Relation rel, mpq_class rhs, bool value = true) {
        auto var = allocator.newVar();
        registry.registerParsedTheoryAtom(var, NullExpr, TheoryId::LIA,
            LinearAtomPayload{lhs, rel, RealValue::fromMpq(rhs)});
        return {NullExpr, -1, rel, value, std::move(lhs), std::move(rhs), SatLit{var, value}};
    }
    bool holds(SatLit lit, const Values& values) const {
        const auto* r = registry.findBySatVar(lit.var);
        if (!r) throw std::logic_error("unregistered literal");
        const auto& p = std::get<LinearAtomPayload>(r->payload);
        const bool truth = compare(p.rel, eval(p.lhs, values), p.rhs.asRational());
        return lit.sign ? truth : !truth;
    }
    bool holds(const TheoryLemma& lemma, const Values& values) const {
        for (const auto lit : lemma.lits) if (holds(lit, values)) return true;
        return false;
    }
};
}

TEST_CASE("Linear predicate projection: weaker signed endpoints reuse existing atoms") {
    Fixture f;
    const LinearFormKey x{{{"x", 1}}};
    const auto strict = f.atom(x, Relation::Gt, 2).lit;
    const auto weak = f.atom(x, Relation::Geq, 1).lit;
    const auto upperComplement = f.atom(x, Relation::Geq, 4).lit.negated();
    const auto count = f.registry.numAtomVars();
    CHECK_FALSE(f.registry.findLinearLiteral(x, Relation::Leq, 3));
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Leq, 3) == upperComplement);
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Geq, 2) == weak);
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Gt, 2,
        [&](SatLit literal) { return literal != strict; }) == weak);
    CHECK(f.registry.numAtomVars() == count);

    const auto openUpper = f.atom(x, Relation::Lt, 2).lit;
    auto onlyOpenUpper = [&](SatLit literal) { return literal == openUpper; };
    CHECK_FALSE(f.registry.findImpliedLinearLiteral(x, Relation::Leq, 2, onlyOpenUpper));
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Lt, 2, onlyOpenUpper) == openUpper);
    const auto dynamic = f.registry.getOrCreateLinearBoundAtom(x, Relation::Geq, mpq_class(3, 2), TheoryId::LRA);
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Geq, 2,
        [&](SatLit literal) { return literal == dynamic; }) == dynamic);
    const auto point = f.atom(x, Relation::Eq, 3).lit;
    CHECK(f.registry.findImpliedLinearLiteral(x, Relation::Leq, 2,
        [&](SatLit literal) { return literal.var == point.var; }) == point.negated());
    CHECK_FALSE(f.registry.findImpliedLinearLiteral(x, Relation::Geq, 3,
        [&](SatLit literal) { return literal.var == point.var; }));
    CHECK_FALSE(f.registry.findImpliedLinearLiteral(x, Relation::Eq, 2));
    CHECK_FALSE(f.registry.findImpliedLinearLiteral({{{"other", 1}}}, Relation::Leq, 3));
    const auto after = f.registry.numAtomVars();
    CHECK_FALSE(f.registry.findImpliedLinearLiteral(x, Relation::Geq, 2, [](SatLit) { return false; }));
    CHECK(f.registry.numAtomVars() == after);
}

TEST_CASE("Linear predicate projection: exact rational half-lines match semantic counterexamples") {
    Fixture f;
    const LinearFormKey form{{{"x", 1}, {"y", -1}}};
    const mpz_class numerator = (mpz_class(1) << 130) + 7;
    const mpq_class large(numerator, mpz_class(3));
    const std::vector<Relation> bounds{Relation::Lt, Relation::Leq, Relation::Gt, Relation::Geq};
    const std::vector<Relation> predicates{Relation::Eq, Relation::Neq,
        Relation::Lt, Relation::Leq, Relation::Gt, Relation::Geq};
    const std::vector<mpq_class> sources{-2, 0, mpq_class(1, 2), 2, large};
    const std::vector<mpq_class> endpoints{mpq_class(-3, 2), 0, mpq_class(5, 3), large};
    std::vector<ActiveLinearAtom> targets;
    for (auto relation : predicates) for (const auto& endpoint : endpoints)
        targets.push_back(f.atom(form, relation, endpoint));
    const auto count = f.registry.numAtomVars();
    for (auto source : bounds) for (const auto& boundary : sources)
        for (const auto& target : targets) for (bool positive : {false, true}) {
            const SatLit wanted{target.lit.var, positive};
            // All truth regions are separated by these two endpoints. Test
            // their boundaries, interiors and exterior rays independently.
            const std::vector<mpq_class> points{boundary - 1, boundary, boundary + 1,
                target.rhs - 1, target.rhs, target.rhs + 1, (boundary + target.rhs) / 2};
            bool entailed = true;
            for (const auto& point : points)
                if (compare(source, point, boundary) &&
                    !f.holds(wanted, Values{{"x", point}, {"y", 0}})) entailed = false;
            const auto projected = f.registry.findImpliedLinearLiteral(form, source, boundary,
                [&](SatLit literal) { return literal == wanted; });
            CHECK(projected.has_value() == entailed);
            if (projected) CHECK(*projected == wanted);
        }
    CHECK(f.registry.numAtomVars() == count);
}

TEST_CASE("LraSolver: original columns project weaker predicates across backtracking") {
    for (bool lower : {false, true}) for (bool strict : {false, true})
        for (bool positive : {false, true}) {
            Allocator allocator;
            TheoryAtomRegistry registry;
            registry.setContext(&allocator, &allocator);
            LraSolver solver;
            solver.setRegistry(&registry);
            auto atom = [&](LinearFormKey form, Relation relation, const mpq_class& rhs) {
                const auto variable = allocator.newVar();
                registry.registerParsedTheoryAtom(variable, NullExpr, TheoryId::LRA,
                    LinearAtomPayload{form, relation, RealValue::fromMpq(rhs)});
                return SatLit::positive(variable);
            };
            const LinearFormKey x{{{"x", 1}}}, y{{{"y", 1}}}, difference{{{"x", 1}, {"y", -1}}};
            const auto relation = lower ? (strict ? Relation::Gt : Relation::Geq)
                                        : (strict ? Relation::Lt : Relation::Leq);
            const auto first = atom(y, relation, 1), second = atom(difference, relation, 1);
            const auto targetRelation = lower ? Relation::Geq : Relation::Leq;
            const auto registered = atom(x, positive ? targetRelation : negateRelation(targetRelation), lower ? 1 : 3);
            const auto target = positive ? registered : registered.negated();
            const auto count = registry.numAtomVars();
            for (auto literal : {first, second})
                solver.assertLit(*registry.findBySatVar(literal.var), true, 1, literal);
            TheoryLemmaDatabase database;
            REQUIRE(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            const auto lemmas = solver.takeEntailmentPropagations();
            CHECK(std::any_of(lemmas.begin(), lemmas.end(), [&](const auto& lemma) {
                return std::find(lemma.lits.begin(), lemma.lits.end(), target) != lemma.lits.end();
            }));
            for (const auto& lemma : lemmas)
                for (int xn = -8; xn <= 8; ++xn) for (int yn = -8; yn <= 8; ++yn) {
                    const Values values{{"x", mpq_class(xn, 2)}, {"y", mpq_class(yn, 2)}};
                    bool holds = false;
                    for (auto literal : lemma.lits) {
                        const auto& payload = std::get<LinearAtomPayload>(registry.findBySatVar(literal.var)->payload);
                        holds |= compare(payload.rel, eval(payload.lhs, values), payload.rhs.asRational()) == literal.sign;
                    }
                    CHECK(holds);
                }
            solver.backtrackToLevel(0);
            REQUIRE(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            CHECK(solver.takeEntailmentPropagations().empty());
            CHECK(registry.numAtomVars() == count);
            const auto opposite = lower ? Relation::Leq : Relation::Geq;
            const auto newFirst = atom(y, opposite, lower ? -10 : 10);
            const auto newSecond = atom(difference, opposite, lower ? -10 : 10);
            for (auto literal : {newFirst, newSecond})
                solver.assertLit(*registry.findBySatVar(literal.var), true, 1, literal);
            REQUIRE(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            const auto later = solver.takeEntailmentPropagations();
            CHECK(std::any_of(later.begin(), later.end(), [&](const auto& lemma) {
                return std::find(lemma.lits.begin(), lemma.lits.end(), target.negated()) != lemma.lits.end();
            }));
        }
}

TEST_CASE("Linear model phase hints: strict endpoints respect infinitesimals") {
    const std::vector<Relation> relations{Relation::Eq,Relation::Neq,Relation::Lt,
        Relation::Leq,Relation::Gt,Relation::Geq};
    for (bool lower : {true,false}) for (int sign : {-1,1}) {
        CAPTURE(lower);
        CAPTURE(sign);
        Allocator allocator;
        TheoryAtomRegistry registry;
        registry.setContext(&allocator,&allocator);
        LraSolver solver;
        solver.setRegistry(&registry);
        const mpq_class endpoint(lower ? 2 : -2);
        auto atom = [&](const LinearFormKey& lhs, Relation relation, const mpq_class& rhs) {
            const auto variable = allocator.newVar();
            registry.registerParsedTheoryAtom(variable,NullExpr,TheoryId::LRA,
                LinearAtomPayload{lhs,relation,RealValue::fromMpq(rhs)});
            return variable;
        };
        const auto premise = atom({{{"x",1}}},lower ? Relation::Gt : Relation::Lt,endpoint);
        const mpq_class coefficient(3*sign), rhs = coefficient*endpoint;
        std::vector<SatVar> targets;
        for (auto relation : relations) targets.push_back(atom({{{"x",coefficient}}},relation,rhs));
        solver.assertLit(*registry.findBySatVar(premise),true,0,SatLit::positive(premise));
        TheoryLemmaDatabase database;
        REQUIRE(solver.check(database,TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
        const auto model = solver.getModel();
        REQUIRE(model.has_value());
        const mpq_class value(model->assignments.at("x"));
        REQUIRE(compare(lower ? Relation::Gt : Relation::Lt,value,endpoint));
        for (size_t i = 0; i < relations.size(); ++i) {
            const auto evaluated = solver.evalAtomAtModel(targets[i]);
            REQUIRE(evaluated.has_value());
            CHECK(*evaluated == compare(relations[i],coefficient*value,rhs));
        }
    }
}

TEST_CASE("Linear model phase hints: large rational endpoints preserve unit differences") {
    Allocator allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator,&allocator);
    LraSolver solver;
    solver.setRegistry(&registry);
    const mpz_class integer = mpz_class(1)<<200;
    const mpq_class endpoint(integer), actual = endpoint+1;
    const LinearFormKey x{{{"x",1}}};
    const auto premise = allocator.newVar();
    registry.registerParsedTheoryAtom(premise,NullExpr,TheoryId::LRA,
        LinearAtomPayload{x,Relation::Eq,RealValue::fromMpq(actual)});
    std::vector<SatVar> targets;
    const std::vector<Relation> relations{Relation::Eq,Relation::Neq,Relation::Lt,
        Relation::Leq,Relation::Gt,Relation::Geq};
    for (auto relation : relations) {
        const auto variable = allocator.newVar();
        registry.registerParsedTheoryAtom(variable,NullExpr,TheoryId::LRA,
            LinearAtomPayload{x,relation,RealValue::fromMpq(endpoint)});
        targets.push_back(variable);
    }
    solver.assertLit(*registry.findBySatVar(premise),true,0,SatLit::positive(premise));
    TheoryLemmaDatabase database;
    REQUIRE(solver.check(database,TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
    for (size_t i = 0; i < relations.size(); ++i) {
        const auto evaluated = solver.evalAtomAtModel(targets[i]);
        REQUIRE(evaluated.has_value());
        CHECK(*evaluated == compare(relations[i],actual,endpoint));
    }
}

TEST_CASE("LiaSolver: partial checks leave integer search to full effort") {
    for (int divisor : {2, 3}) for (int sign : {-1, 1}) {
        CAPTURE(divisor);
        CAPTURE(sign);
        Fixture f;
        LiaSolver solver;
        solver.setRegistry(&f.registry);
        const auto fractional = f.atom({{{"x", sign * divisor}}}, Relation::Geq, 1);
        const auto endpoint = f.atom({{{"x", 1}}}, sign > 0 ? Relation::Leq : Relation::Geq, sign);
        for (const auto& atom : {fractional, endpoint})
            solver.assertLit(*f.registry.findBySatVar(atom.lit.var), true, 0, atom.lit);
        const auto atoms = f.registry.numAtomVars();
        const auto variables = f.allocator.next;
        TheoryLemmaDatabase database;
        for (int repeat = 0; repeat < 3; ++repeat) {
            CHECK(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Unknown);
            CHECK(f.registry.numAtomVars() == atoms);
            CHECK(f.allocator.next == variables);
        }
        REQUIRE(solver.check(database, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
        const auto model = solver.getModel();
        REQUIRE(model);
        const mpq_class value(model->assignments.at("x"));
        CHECK(value.get_den() == 1);
        CHECK(f.holds(fractional.lit, {{"x", value}}));
        CHECK(f.holds(endpoint.lit, {{"x", value}}));
        CHECK(f.registry.numAtomVars() == atoms);
    }
}

TEST_CASE("IntegerReasoner: partial checks do not synthesize vocabulary") {
    Fixture f;
    const auto tighten = f.atom({{{"x", 2}}}, Relation::Leq, 3);
    const auto impossible = f.atom({{{"y", 2}}}, Relation::Eq, 1);
    const auto atoms = f.registry.numAtomVars();
    const auto conflict = f.reasoner.run({tighten, impossible}, TheoryEffort::Standard);
    REQUIRE(conflict);
    CHECK(conflict->kind == TheoryCheckResult::Kind::Conflict);
    REQUIRE(conflict->conflictOpt);
    CHECK(conflict->conflictOpt->clause == std::vector<SatLit>{impossible.lit});
    CHECK(f.registry.numAtomVars() == atoms);
    // The default call retains its complete refinement behavior.
    const auto lemma = f.reasoner.run({tighten});
    REQUIRE(lemma);
    REQUIRE(lemma->lemmaOpt);
    for (int x = -4; x <= 4; ++x) CHECK(f.holds(*lemma->lemmaOpt, {{"x", x}}));
}

TEST_CASE("LiaSolver: primitive coupled rows reach a validated integer repair") {
    Fixture f;
    LiaSolver solver;
    solver.setRegistry(&f.registry);
    const auto equation = f.atom({{{"x", 2}, {"y", 1}}}, Relation::Eq, 1);
    const auto xLower = f.atom({{{"x", 1}}}, Relation::Geq, 0);
    const auto yLower = f.atom({{{"y", 1}}}, Relation::Geq, 0);
    for (const auto& atom : {equation, xLower, yLower})
        solver.assertLit(*f.registry.findBySatVar(atom.lit.var), true, 0, atom.lit);
    const auto atoms = f.registry.numAtomVars();
    TheoryLemmaDatabase database;
    CHECK(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Unknown);
    CHECK(f.registry.numAtomVars() == atoms);
    REQUIRE(solver.check(database, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = solver.getModel();
    REQUIRE(model);
    const Values values{{"x", mpq_class(model->assignments.at("x"))},
                        {"y", mpq_class(model->assignments.at("y"))}};
    for (const auto& [name, value] : values) { (void)name; CHECK(value.get_den() == 1); }
    for (const auto& atom : {equation, xLower, yLower}) CHECK(f.holds(atom.lit, values));
    CHECK(f.registry.numAtomVars() == atoms);
}

TEST_CASE("LraSolver: ordinary propagation preserves the registered vocabulary") {
    for (int variant = 0; variant < 4; ++variant) {
        CAPTURE(variant);
        Allocator allocator;
        TheoryAtomRegistry registry;
        registry.setContext(&allocator, &allocator);
        LraSolver solver;
        solver.setRegistry(&registry);
        const bool strict = variant == 3;
        auto registerAtom = [&](LinearFormKey lhs, Relation relation, int rhs) {
            const auto variable = allocator.newVar();
            registry.registerParsedTheoryAtom(variable, NullExpr, TheoryId::LRA,
                LinearAtomPayload{lhs, relation, RealValue::fromMpq(mpq_class(rhs))});
            return variable;
        };
        const LinearFormKey x{{{"x", 1}}}, y{{{"y", 1}}}, sum{{{"x", 1}, {"y", 1}}};
        const auto first = registerAtom(x, strict ? Relation::Gt : Relation::Leq, 1);
        const auto second = registerAtom(y, strict ? Relation::Gt : Relation::Leq, 2);
        const auto weak = registerAtom(sum, strict ? Relation::Geq : Relation::Leq, strict ? -10 : 10);
        std::optional<SatLit> target;
        if (variant) {
            const auto relation = variant == 2 ? Relation::Gt : Relation::Leq;
            const auto variable = registerAtom(sum, relation, 3);
            target = variant == 1 ? SatLit::positive(variable) : SatLit::negative(variable);
        }
        const auto missingSize = registry.numAtomVars();
        CHECK_FALSE(registry.findLinearLiteral(sum, Relation::Eq, 999).has_value());
        CHECK(registry.numAtomVars() == missingSize);
        for (const auto variable : {first, second, weak})
            solver.assertLit(*registry.findBySatVar(variable), true, 0, SatLit::positive(variable));
        const auto atomCount = registry.numAtomVars();
        const auto variableCount = allocator.next;
        TheoryLemmaDatabase database;
        for (int repeat = 0; repeat < 3; ++repeat) {
            REQUIRE(solver.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            const auto propagations = solver.takeEntailmentPropagations();
            CHECK(registry.numAtomVars() == atomCount);
            CHECK(allocator.next == variableCount);
            if (!target) { CHECK(propagations.empty()); continue; }
            CHECK(std::any_of(propagations.begin(), propagations.end(), [&](const auto& lemma) {
                return std::find(lemma.lits.begin(), lemma.lits.end(), *target) != lemma.lits.end();
            }));
            for (const auto& lemma : propagations) {
                for (int xn = -6; xn <= 8; ++xn) for (int yn = -6; yn <= 8; ++yn) {
                    const Values values{{"x", mpq_class(xn, 2)}, {"y", mpq_class(yn, 2)}};
                    bool holds = false;
                    for (const auto literal : lemma.lits) {
                        const auto* record = registry.findBySatVar(literal.var);
                        REQUIRE(record != nullptr);
                        const auto& payload = std::get<LinearAtomPayload>(record->payload);
                        holds |= compare(payload.rel, eval(payload.lhs, values), payload.rhs.asRational()) == literal.sign;
                    }
                    CHECK(holds);
                }
            }
        }
    }
}

TEST_CASE("BoundAxiomGenerator: selecting LIA preserves other theories and the input vocabulary") {
    struct Clauses : Allocator {
        std::vector<std::vector<SatLit>> clauses;
        void addClause(const std::vector<SatLit>& clause) override { clauses.push_back(clause); }
    } allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator, &allocator);
    const LinearFormKey form{{{"x", 1}}};
    const auto first = registry.getOrCreateLinearBoundAtom(form, Relation::Leq, 1, TheoryId::LIA);
    const auto second = registry.getOrCreateLinearBoundAtom(form, Relation::Leq, 2, TheoryId::LIA);
    const auto realFirst = registry.getOrCreateLinearBoundAtom(form, Relation::Geq, -1, TheoryId::LRA);
    registry.getOrCreateLinearBoundAtom(form, Relation::Geq, -2, TheoryId::LRA);
    const auto count = allocator.next;
    CHECK(BoundAxiomGenerator::generate(registry, allocator, TheoryId::LIA) == 1);
    REQUIRE(allocator.clauses.size() == 1);
    CHECK(allocator.clauses[0] == std::vector<SatLit>{first.negated(), second});
    CHECK(allocator.next == count);
    CHECK(registry.numAtomVars() == count);
    for (const auto& clause : allocator.clauses)
        for (const auto literal : clause) CHECK(literal.var < realFirst.var);
    // Check the actual emitted clause, not only an expected implementation shape.
    for (int n = -12; n <= 12; ++n) {
        const mpq_class x(n, 3);
        bool holds = false;
        for (const auto literal : allocator.clauses[0]) {
            const auto* record = registry.findBySatVar(literal.var);
            REQUIRE(record != nullptr);
            const auto& atom = std::get<LinearAtomPayload>(record->payload);
            holds |= compare(atom.rel, x, atom.rhs.asRational()) == literal.sign;
        }
        CHECK(holds);
    }
}

TEST_CASE("BoundAxiomGenerator: eager family size preserves the default and original vocabulary") {
    struct RecordingAllocator : Allocator {
        std::vector<std::vector<SatLit>> clauses;
        void addClause(const std::vector<SatLit>& clause) override { clauses.push_back(clause); }
    } allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator, &allocator);
    for (const auto& name : {"x", "y"}) for (int rhs = 0; rhs < (name[0] == 'x' ? 3 : 2); ++rhs)
        registry.getOrCreateLinearBoundAtom(LinearFormKey{{{name, 1}}}, Relation::Leq, rhs, TheoryId::LIA);
    const auto variables = registry.numAtomVars();
    CHECK(BoundAxiomGenerator::generate(registry, allocator, TheoryId::LIA, 3) == 3);
    CHECK(allocator.clauses.size() == 3);
    for (const auto& clause : allocator.clauses) for (int n = -4; n <= 8; ++n) {
        mpq_class point(n, 2); point.canonicalize();
        bool holds = false;
        for (const auto literal : clause) {
            const auto* atom = registry.findBySatVar(literal.var);
            REQUIRE(atom != nullptr);
            const auto& payload = std::get<LinearAtomPayload>(atom->payload);
            CHECK(payload.lhs.terms.front().first == "x");
            holds |= compare(payload.rel, point, payload.rhs.asRational()) == literal.sign;
        }
        CHECK(holds);
    }
    allocator.clauses.clear();
    CHECK(BoundAxiomGenerator::generate(registry, allocator, TheoryId::LIA) == 4);
    CHECK(allocator.clauses.size() == 4);
    CHECK(registry.numAtomVars() == variables);
}

TEST_CASE("LIA: missing dynamic registration cannot dereference an absent branch registrar") {
    const LinearFormKey doubled{{{"x", 2}}};
    LiaSolver solver;
    TheoryLemmaDatabase database;
    solver.assertLit(TheoryAtomRecord{1, TheoryId::LIA, false, 1,
        LinearAtomPayload{doubled, Relation::Eq, RealValue::fromMpq(1)}}, true, 0, SatLit::positive(1));
    // The rational relaxation is fractional; the integer gcd refutation still
    // applies without a SAT registrar to allocate branch literals.
    CHECK((solver.check(database).kind == TheoryCheckResult::Kind::Conflict));
    LiaSolver disequalitySolver;
    const LinearFormKey unit{{{"x", 1}}};
    disequalitySolver.assertLit(TheoryAtomRecord{2, TheoryId::LIA, false, 2,
        LinearAtomPayload{unit, Relation::Neq, RealValue::fromMpq(0)}}, true, 0, SatLit::positive(2));
    CHECK((disequalitySolver.check(database, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Unknown));
}

TEST_CASE("linear propagation: borrowed endpoint patterns match independent truth and preserve owning values") {
    const Relation relations[] = {Relation::Eq, Relation::Neq, Relation::Lt, Relation::Leq, Relation::Gt, Relation::Geq};
    for (const auto relation : relations) for (const bool truth : {false, true}) for (const bool integral : {false, true}) {
        const auto bounds = LinearAtomManager::effectiveBoundViews(relation, truth, integral);
        const auto effective = truth ? relation : negateRelation(relation);
        if (effective == Relation::Neq) {
            CHECK(bounds.lower == nullptr);
            CHECK(bounds.upper == nullptr);
            continue;
        }
        for (int numerator = -8; numerator <= 8; ++numerator) {
            mpq_class point(numerator, integral ? 1 : 2); point.canonicalize();
            const DeltaRational value(point);
            const bool accepted = (!bounds.lower || value >= *bounds.lower) && (!bounds.upper || value <= *bounds.upper);
            CHECK(accepted == (compare(relation, point, mpq_class(0)) == truth));
        }
    }
    const auto zero = LinearAtomManager::effectiveBoundViews(Relation::Eq, true, false);
    auto owned = LinearAtomManager::effectiveBounds(Relation::Eq, true, false);
    *owned.lower = DeltaRational(99);
    CHECK(*zero.lower == DeltaRational(0));
    CHECK(*zero.upper == DeltaRational(0));
    const auto strict = LinearAtomManager::effectiveBoundViews(Relation::Lt, true, false);
    CHECK(*strict.upper == DeltaRational(0, -1));
    CHECK(*zero.lower == DeltaRational(0));
}

TEST_CASE("linear propagation: auxiliary lookup owns new forms and reuses borrowed equal forms after rehash") {
    LinearAtomManager manager;
    GeneralSimplex gs;
    LinearFormKey input{{{"lookup-x", mpq_class(3, 2)}, {"lookup-y", mpq_class(-1, 2)}}};
    mpq_class rhs(2, 3);
    const auto original = input;
    const int aux = manager.getOrCreateAuxVar(gs, input, rhs);
    input.terms.front().second = 99;
    rhs = 17;
    CHECK(manager.getOrCreateAuxVar(gs, input, rhs) != aux);
    for (int value = 0; value < 96; ++value) manager.getOrCreateAuxVar(gs, original, mpq_class(value));
    const auto count = gs.numVars();
    CHECK(manager.getOrCreateAuxVar(gs, original, mpq_class(2, 3)) == aux);
    CHECK(gs.numVars() == count);
    LinearFormKey recovered;
    mpq_class recoveredRhs;
    REQUIRE(manager.auxForm(aux, recovered, recoveredRhs));
    CHECK(recovered == original);
    CHECK(recoveredRhs == mpq_class(2, 3));
    for (auto [name, value] : {std::pair{"lookup-x", 2}, std::pair{"lookup-y", 3}}) {
        const auto var = manager.findVarIndex(name);
        const BoundInfo pin(BoundValue(DeltaRational(value)), SatLit::positive(1));
        REQUIRE(gs.assertLower(var, pin));
        REQUIRE(gs.assertUpper(var, pin));
    }
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    CHECK(gs.value(aux) == DeltaRational(mpq_class(5, 6))); // 3*2/2 - 3/2 - 2/3
}

TEST_CASE("LIA: decision hints use exact values and leave unregistered coordinates untouched") {
    Allocator allocator;
    TheoryAtomRegistry registry;
    registry.setContext(&allocator, &allocator);
    const LinearFormKey form{{{"x", 1}}};
    const mpq_class large(mpz_class("9007199254740992"));
    const auto source = registry.getOrCreateLinearBoundAtom(form, Relation::Eq, large, TheoryId::LIA);
    const auto equal = registry.getOrCreateLinearBoundAtom(form, Relation::Eq, large + 1, TheoryId::LIA);
    const auto strict = registry.getOrCreateLinearBoundAtom(form, Relation::Lt, large + 1, TheoryId::LIA);
    const auto missing = registry.getOrCreateLinearBoundAtom(LinearFormKey{{{"y", 1}}}, Relation::Leq, 1, TheoryId::LIA);
    LiaSolver solver;
    solver.setRegistry(&registry);
    solver.assertLit(*registry.findBySatVar(source.var), true, 1, source);
    TheoryLemmaDatabase db;
    REQUIRE(solver.check(db).kind == TheoryCheckResult::Kind::Consistent);
    const auto size = registry.numAtomVars();
    REQUIRE(solver.evalAtomAtModel(equal.var).has_value());
    CHECK_FALSE(*solver.evalAtomAtModel(equal.var));
    REQUIRE(solver.evalAtomAtModel(strict.var).has_value());
    CHECK(*solver.evalAtomAtModel(strict.var));
    CHECK_FALSE(solver.evalAtomAtModel(missing.var).has_value());
    CHECK(registry.numAtomVars() == size);
}

TEST_CASE("IntegerReasoner soundness: normalization preserves integer witnesses") {
    for (const auto& a : {mpq_class(-3,2), mpq_class(-1,2), mpq_class(1,2), mpq_class(2,3), mpq_class(2)})
    for (const auto& b : {mpq_class(-2), mpq_class(-1,3), mpq_class(0), mpq_class(1,2), mpq_class(1), mpq_class(2)})
    for (auto rel : {Relation::Eq, Relation::Neq, Relation::Leq, Relation::Geq, Relation::Lt, Relation::Gt})
    for (bool value : {false, true}) {
        LinearFormKey lhs{{{"x", a}}};
        auto normalized = IntegerReasoner::normalize(lhs, b, rel, value);
        REQUIRE(normalized.has_value());
        for (int x = -4; x <= 4; ++x) {
            CAPTURE(a); CAPTURE(b); CAPTURE(rel); CAPTURE(value); CAPTURE(x);
            const bool original = compare(rel, mpq_class(a*x), b) == value;
            CHECK(compare(normalized->rel, eval(normalized->lhs, {{"x",x}}), normalized->rhs) == original);
        }
    }
}

TEST_CASE("IntegerReasoner soundness: rational strict bound lemmas preserve witnesses") {
    for (bool value : {false, true}) {
        Fixture f;
        // True x/2 < 1 admits x=1; false x/2 <= 0 admits x=1.
        auto atom = f.atom(LinearFormKey{{{"x",mpq_class(1,2)}}},
            value ? Relation::Lt : Relation::Leq, value ? 1 : 0, value);
        auto result = f.reasoner.run({atom});
        REQUIRE(result.has_value());
        REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
        REQUIRE(result->lemmaOpt.has_value());
        const Values witness{{"x",1}};
        REQUIRE(f.holds(atom.lit, witness));
        CHECK(f.holds(*result->lemmaOpt, witness));
    }
}

TEST_CASE("IntegerReasoner soundness: disequalities do not imply one-sided bounds") {
    for (bool value : {false, true}) {
        Fixture f;
        auto atom = f.atom(LinearFormKey{{{"x",2}}}, value ? Relation::Neq : Relation::Eq, 4, value);
        const Values witness{{"x",3}};
        REQUIRE(f.holds(atom.lit, witness));
        if (auto result = f.reasoner.run({atom})) {
            REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
            REQUIRE(result->lemmaOpt.has_value());
            CHECK(f.holds(*result->lemmaOpt, witness));
        }
    }
}

TEST_CASE("IntegerReasoner soundness: negative gcd bound has an exact lattice tightening") {
    Fixture f;
    auto atom = f.atom(LinearFormKey{{{"x",2},{"y",4}}}, Relation::Leq, -1);
    auto normalized = IntegerReasoner::normalize(atom.lhs, atom.rhs, atom.rel, true);
    REQUIRE(normalized.has_value());
    auto lemma = f.reasoner.checkGcdInequalityTightening(*normalized, atom.lit);
    REQUIRE(lemma.has_value());
    REQUIRE(lemma->lits.size() == 2);
    // The tight lattice bound is -2, between the infeasible real values -2 and -1.
    CHECK_FALSE(f.holds(lemma->lits.back(), {{"x",mpq_class(-3,4)},{"y",0}}));
    CHECK(f.holds(lemma->lits.back(), {{"x",-1},{"y",0}}));
    for (int x=-3; x<=3; ++x) for (int y=-3; y<=3; ++y)
        CHECK(f.holds(*lemma, {{"x",x},{"y",y}}));
}

TEST_CASE("IntegerReasoner soundness: LIA core preserves a rational-bound countermodel") {
    Fixture f;
    LiaSolver solver;
    solver.setRegistry(&f.registry);
    const auto a = f.atom(LinearFormKey{{{"x",mpq_class(1,2)}}}, Relation::Lt, 1);
    const auto b = f.atom(LinearFormKey{{{"y",2}}}, Relation::Geq, 1);
    const Values witness{{"x",1},{"y",1}};
    for (const auto& atom : {a,b}) {
        REQUIRE(f.holds(atom.lit, witness));
        solver.assertLit(*f.registry.findBySatVar(atom.lit.var), true, 0, atom.lit);
    }
    TheoryLemmaDatabase lemmas;
    const auto atoms = f.registry.numAtomVars();
    CHECK(solver.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Unknown);
    CHECK(f.registry.numAtomVars() == atoms);
    REQUIRE(solver.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = solver.getModel();
    REQUIRE(model);
    const Values values{{"x", mpq_class(model->assignments.at("x"))},
                        {"y", mpq_class(model->assignments.at("y"))}};
    CHECK(f.holds(a.lit, values));
    CHECK(f.holds(b.lit, values));
    // Pin the original countermodel too: validating a different integer point
    // alone would not catch a bound rule that accidentally excluded x=1.
    for (const auto& name : {"x", "y"}) {
        const auto pin = f.atom(LinearFormKey{{{name, 1}}}, Relation::Eq, 1);
        solver.assertLit(*f.registry.findBySatVar(pin.lit.var), true, 0, pin.lit);
    }
    REQUIRE(solver.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("IntegerReasoner soundness: shared integer atom normalization preserves witnesses") {
    for (const auto rel : {Relation::Lt, Relation::Gt}) {
        ZeroLinearConstraint c;
        c.expr.terms = {{"x",mpq_class(1,2)}};
        c.expr.constant = rel == Relation::Lt ? -1 : 0;
        c.rel = rel;
        c.sort = SortKind::Int;
        const auto out = LinearConstraintNormalizer::toLinearAtomSpec(c);
        const mpq_class x = 1;
        REQUIRE(compare(c.rel, mpq_class(x/2+c.expr.constant), 0));
        CHECK(compare(out.rel, eval(out.lhs, {{"x",x}}), out.rhs));
    }
}
