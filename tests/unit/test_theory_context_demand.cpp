#include <doctest/doctest.h>
#include "search/coordination/TheoryManager.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <map>

using namespace xolver;

namespace {
struct CountingAssignment : TheoryAssignmentView {
    std::map<SatVar, LitValue> values;
    mutable int queries = 0;
    LitValue value(SatLit literal) const override {
        ++queries;
        const auto it = values.find(literal.var);
        if (it == values.end() || it->second == LitValue::Unknown) return LitValue::Unknown;
        const bool positive = it->second == LitValue::True;
        return positive == literal.sign ? LitValue::True : LitValue::False;
    }
};

class PassiveTheory : public TheorySolver {
public:
    explicit PassiveTheory(TheoryId theory = TheoryId::LRA) : theory_(theory) {}
    TheoryId id() const override { return theory_; }
    void push() override {}
    void pop(uint32_t) override {}
    void backtrackToLevel(int) override {}
    void reset() override {}
    void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
    TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
        return TheoryCheckResult::consistent();
    }
private:
    TheoryId theory_;
};

class ContextReader : public PassiveTheory {
public:
    explicit ContextReader(TheoryId theory) : PassiveTheory(theory) {}
    bool needsActiveLinearContext() const override { return true; }
    void setActiveLinearContext(const std::vector<ActiveLinearConstraint>* context) override {
        current = context;
    }
    TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
        REQUIRE(current != nullptr);
        observed = *current;
        return TheoryCheckResult::consistent();
    }
    const std::vector<ActiveLinearConstraint>* current = nullptr;
    std::vector<ActiveLinearConstraint> observed;
};

void registerLinear(TheoryAtomRegistry& registry, SatVar variable) {
    LinearFormKey form;
    form.terms.emplace_back("x" + std::to_string(variable), mpq_class(3, 7));
    registry.registerParsedTheoryAtom(variable, NullExpr, TheoryId::LRA,
        LinearAtomPayload{form, Relation::Leq, RealValue::fromMpq(mpq_class(variable, 5))});
}
}

TEST_CASE("TheoryManager: theories without context consumers avoid assignment scans") {
    TheoryManager manager;
    TheoryAtomRegistry registry;
    CountingAssignment assignment;
    TheoryLemmaDatabase lemmas;
    for (SatVar variable = 1; variable <= 64; ++variable) {
        registerLinear(registry, variable);
        assignment.values[variable] = LitValue::True;
    }
    manager.setRegistry(&registry);
    manager.setAssignmentView(&assignment);
    manager.registerSolver(std::make_unique<PassiveTheory>());
    REQUIRE(manager.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(assignment.queries == 0);
    // The explicit collection API remains available and retains its meaning.
    const auto snapshot = manager.collectActiveLinearConstraints();
    CHECK(snapshot.size() == 64);
    CHECK(assignment.queries == 64);
}

TEST_CASE("TheoryManager: context consumers share a fresh snapshot across state changes") {
    TheoryManager manager;
    TheoryAtomRegistry registry;
    CountingAssignment assignment;
    TheoryLemmaDatabase lemmas;
    for (SatVar variable = 1; variable <= 3; ++variable) registerLinear(registry, variable);
    assignment.values = {{1, LitValue::True}, {2, LitValue::False}};
    manager.setRegistry(&registry);
    manager.setAssignmentView(&assignment);
    auto firstOwner = std::make_unique<ContextReader>(TheoryId::NIRA);
    auto secondOwner = std::make_unique<ContextReader>(TheoryId::NRA);
    auto* first = firstOwner.get();
    auto* second = secondOwner.get();
    manager.registerSolver(std::move(firstOwner));
    manager.registerSolver(std::move(secondOwner));
    REQUIRE(manager.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(assignment.queries == 3);
    CHECK(first->current == second->current);
    REQUIRE(first->observed.size() == 2);
    REQUIRE(second->observed.size() == 2);
    CHECK(first->observed[0].reasonLit == SatLit::positive(1));
    CHECK(first->observed[1].reasonLit == SatLit::negative(2));
    CHECK(first->observed[1].payload.rel == Relation::Gt);
    CHECK(first->observed[1].payload.lhs == second->observed[1].payload.lhs);

    assignment.values[1] = LitValue::Unknown;
    assignment.values[2] = LitValue::True;
    assignment.values[3] = LitValue::False;
    manager.backtrackToLevel(0);
    REQUIRE(manager.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(assignment.queries == 6);
    REQUIRE(first->observed.size() == 2);
    CHECK(first->observed[0].reasonLit == SatLit::positive(2));
    CHECK(first->observed[0].payload.rel == Relation::Leq);
    CHECK(first->observed[1].reasonLit == SatLit::negative(3));

    registerLinear(registry, 4);
    assignment.values[4] = LitValue::True;
    REQUIRE(manager.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(assignment.queries == 10);
    REQUIRE(first->observed.size() == 3);
    CHECK(first->observed[2].reasonLit == SatLit::positive(4));

    manager.clearSolvers();
    manager.registerSolver(std::make_unique<PassiveTheory>());
    REQUIRE(manager.check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(assignment.queries == 10);
}
