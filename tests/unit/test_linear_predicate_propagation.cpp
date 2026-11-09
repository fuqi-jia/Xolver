#include <doctest/doctest.h>
#include "search/linear/LinearPredicatePropagation.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/coordination/TheoryManager.h"
#include <algorithm>
#include <stdexcept>

using namespace xolver;

namespace {
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

bool compare(Relation relation, const mpq_class& lhs, const mpq_class& rhs) {
    switch (relation) {
        case Relation::Eq: return lhs == rhs;
        case Relation::Neq: return lhs != rhs;
        case Relation::Lt: return lhs < rhs;
        case Relation::Leq: return lhs <= rhs;
        case Relation::Gt: return lhs > rhs;
        case Relation::Geq: return lhs >= rhs;
    }
    throw std::logic_error("invalid relation");
}

struct Fixture {
    Allocator allocator;
    TheoryAtomRegistry registry;
    LinearPredicatePropagation propagation;
    TheoryLemmaDatabase lemmas;
    Fixture() { registry.setContext(&allocator, &allocator); }
    SatLit atom(Relation relation, const mpq_class& rhs, int sign = 1,
                TheoryId theory = TheoryId::LRA) {
        return registry.getOrCreateLinearBoundAtom(LinearFormKey{{{"x", sign}}}, relation, rhs, theory);
    }
    void assertLit(SatLit literal, int level = 0) {
        propagation.assertLit(registry, *registry.findBySatVar(literal.var), literal, level);
    }
    std::optional<TheoryCheckResult> check() { return propagation.check(registry, nullptr, lemmas); }
    bool truth(SatLit literal, const mpq_class& x) const {
        const auto* record = registry.findBySatVar(literal.var);
        if (!record) throw std::logic_error("unknown predicate");
        const auto& p = std::get<LinearAtomPayload>(record->payload);
        return compare(p.rel, mpq_class(p.lhs.terms.front().second * x), p.rhs.asRational()) == literal.sign;
    }
    std::vector<TheoryLemma> drain() {
        std::vector<TheoryLemma> result;
        for (size_t count = 0; count < 100; ++count) {
            auto next = check();
            if (!next) return result;
            REQUIRE(next->kind == TheoryCheckResult::Kind::Lemma);
            result.push_back(*next->lemmaOpt);
            lemmas.insertIfNew(*next->lemmaOpt);
        }
        FAIL("predicate propagation failed to drain");
        return result;
    }
};

std::vector<mpq_class> cells(std::vector<mpq_class> endpoints) {
    std::sort(endpoints.begin(), endpoints.end());
    endpoints.erase(std::unique(endpoints.begin(), endpoints.end()), endpoints.end());
    std::vector<mpq_class> points{endpoints.front() - 1, endpoints.back() + 1};
    for (size_t i = 0; i < endpoints.size(); ++i) {
        points.push_back(endpoints[i]);
        if (i) points.push_back((endpoints[i - 1] + endpoints[i]) / 2);
    }
    return points;
}
}

TEST_CASE("Linear predicate propagation: all single-source consequences match exact rational cells") {
    const Relation relations[] = {Relation::Eq, Relation::Neq, Relation::Lt,
                                   Relation::Leq, Relation::Gt, Relation::Geq};
    const std::vector<mpq_class> endpoints{mpq_class(-2, 3), 0, mpq_class(1, 1000003)};
    size_t emitted = 0;
    for (const auto theory : {TheoryId::LIA, TheoryId::LRA, TheoryId::NRA})
        for (const auto sourceRelation : relations) for (const auto targetRelation : relations)
            for (const auto& sourceValue : endpoints) for (const auto& targetValue : endpoints)
                for (const int sign : {-1, 1}) for (const bool positive : {false, true}) {
                    Fixture f;
                    const auto source = f.atom(sourceRelation, sourceValue, 1, theory);
                    const auto target = f.atom(targetRelation, targetValue, sign, theory);
                    const SatLit premise{source.var, positive};
                    const auto size = f.registry.numAtomVars();
                    f.assertLit(premise);
                    const auto result = f.check();
                    CHECK(f.registry.numAtomVars() == size);
                    CHECK(f.allocator.next == size);
                    const auto points = cells({sourceValue, mpq_class(sign * targetValue)});
                    bool canBeTrue = false, canBeFalse = false;
                    for (const auto& x : points) if (f.truth(premise, x)) {
                        canBeTrue |= f.truth(target, x);
                        canBeFalse |= !f.truth(target, x);
                    }
                    if (source.var == target.var) { CHECK_FALSE(result); continue; }
                    CHECK(static_cast<bool>(result) == (canBeTrue != canBeFalse));
                    if (!result) continue;
                    ++emitted;
                    REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
                    REQUIRE(result->lemmaOpt.has_value());
                    CHECK(result->lemmaOpt->lits.back() == SatLit{target.var, canBeTrue});
                    for (const auto& x : points) {
                        bool valid = false;
                        for (const auto literal : result->lemmaOpt->lits) valid |= f.truth(literal, x);
                        CHECK(valid);
                    }
                }
    CHECK(emitted > 1000);
}

TEST_CASE("Linear predicate propagation: two closed endpoints imply an existing equality") {
    for (const auto relation : {Relation::Eq, Relation::Neq}) {
        Fixture f;
        const auto lo = f.atom(Relation::Geq, mpq_class(2, 7));
        const auto hi = f.atom(Relation::Geq, mpq_class(-2, 7), -1);
        const auto point = f.atom(relation, mpq_class(2, 7));
        f.assertLit(lo, 1); f.assertLit(hi, 2);
        const auto result = f.check();
        REQUIRE(result.has_value());
        REQUIRE(result->kind == TheoryCheckResult::Kind::Lemma);
        CHECK(result->lemmaOpt->lits.size() == 3);
        CHECK(result->lemmaOpt->lits.back() == SatLit{point.var, relation == Relation::Eq});
        CHECK(f.registry.numAtomVars() == 3);
    }
}

TEST_CASE("Linear predicate propagation: strict emptiness and excluded singleton have exact conflicts") {
    for (const bool hole : {false, true}) {
        Fixture f;
        const auto lo = f.atom(hole ? Relation::Geq : Relation::Gt, 0);
        const auto hi = f.atom(Relation::Leq, 0);
        f.assertLit(lo); f.assertLit(hi);
        if (hole) f.assertLit(f.atom(Relation::Neq, 0));
        const auto result = f.check();
        REQUIRE(result.has_value());
        REQUIRE(result->kind == TheoryCheckResult::Kind::Conflict);
        CHECK(result->conflictOpt->clause.size() == (hole ? 3 : 2));
        for (const auto& x : cells({0})) {
            bool valid = false;
            for (const auto literal : result->conflictOpt->clause) valid |= f.truth(literal, x);
            CHECK(valid);
        }
    }
}

TEST_CASE("Linear predicate propagation: interior withdrawal discards old bounds and pending work") {
    Fixture f;
    const auto upper = f.atom(Relation::Leq, 0);
    const auto lower = f.atom(Relation::Geq, 2);
    const auto target = f.atom(Relation::Lt, 1);
    f.assertLit(upper, 4); f.assertLit(lower, 1);
    const auto conflict = f.check();
    REQUIRE(conflict.has_value());
    REQUIRE(conflict->kind == TheoryCheckResult::Kind::Conflict);
    f.propagation.backtrackToLevel(1);
    const auto consequences = f.drain();
    CHECK(std::any_of(consequences.begin(), consequences.end(), [&](const auto& lemma) {
        return lemma.lits.back() == target.negated();
    }));
    f.propagation.backtrackToLevel(0);
    CHECK_FALSE(f.check());
}

TEST_CASE("Linear predicate propagation: replacement and late atoms preserve their source lifetimes") {
    Fixture f;
    const auto source = f.atom(Relation::Leq, 0);
    f.assertLit(source, 2);
    CHECK_FALSE(f.check());
    const auto target = f.atom(Relation::Leq, 1);
    const auto other = f.atom(Relation::Leq, 2);
    const auto first = f.check();
    REQUIRE(first.has_value());
    REQUIRE(first->kind == TheoryCheckResult::Kind::Lemma);
    f.lemmas.insertIfNew(*first->lemmaOpt);
    f.assertLit(source.negated(), 1);
    CHECK_FALSE(f.check());
    f.propagation.backtrackToLevel(0);
    CHECK_FALSE(f.check());
    f.assertLit(source, 0);
    const auto remaining = f.drain();
    CHECK(std::any_of(remaining.begin(), remaining.end(), [&](const auto& lemma) {
        return lemma.lits.back() == other || lemma.lits.back() == target;
    }));
    f.assertLit(source, 0);
    CHECK_FALSE(f.check());
    CHECK(f.registry.numAtomVars() == 3);
}

TEST_CASE("Linear predicate propagation: same-name coordinates keep their theory ownership") {
    Fixture f;
    const auto upper = f.atom(Relation::Leq, 0, 1, TheoryId::LRA);
    const auto lower = f.atom(Relation::Geq, 1, 1, TheoryId::LIA);
    f.assertLit(upper); f.assertLit(lower);
    CHECK_FALSE(f.check());
}

TEST_CASE("TheoryManager: original predicate implications precede the complete theory check") {
    struct CountingTheory : TheorySolver {
        int checks = 0;
        TheoryId id() const override { return TheoryId::LRA; }
        void push() override {}
        void pop(uint32_t) override {}
        void reset() override {}
        void backtrackToLevel(int) override {}
        void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
            ++checks;
            return TheoryCheckResult::consistent();
        }
    };
    Fixture f;
    const auto source = f.atom(Relation::Leq, 0);
    const auto target = f.atom(Relation::Leq, 1);
    TheoryManager manager;
    manager.setRegistry(&f.registry);
    auto solver = std::make_unique<CountingTheory>();
    auto* counter = solver.get();
    manager.registerSolver(std::move(solver));
    manager.assertTheoryLit(*f.registry.findBySatVar(source.var), source, 0);
    const auto result = manager.check(f.lemmas, TheoryEffort::Standard);
    REQUIRE(result.kind == TheoryCheckResult::Kind::Lemma);
    CHECK(counter->checks == 0);
    f.lemmas.insertIfNew(*result.lemmaOpt);
    manager.assertTheoryLit(*f.registry.findBySatVar(target.var), target, 0);
    CHECK(manager.check(f.lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(counter->checks == 1);
    CHECK(f.registry.numAtomVars() == 2);
}
