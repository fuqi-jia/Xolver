#include <doctest/doctest.h>
#include "search/linear/IntegerReasoner.h"
#include "search/linear/BoundAxiomGenerator.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "applications/smt/common/lia/LiaSolver.h"
#include "applications/smt/qflra/LraSolver.h"
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
    const auto result = solver.check(lemmas, TheoryEffort::Standard);
    REQUIRE(result.kind == TheoryCheckResult::Kind::Lemma);
    REQUIRE(result.lemmaOpt.has_value());
    CHECK(f.holds(*result.lemmaOpt, witness));
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
