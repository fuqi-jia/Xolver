#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryManager.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
// White-box: SatSolver (CaDiCaL backend) — interface compliance and corner
// cases that downstream theories implicitly rely on (unit propagation,
// assumption-based unsat core, empty clause, single-literal clauses, etc.).
//
// Note: the createSatSolver() factory returns the CaDiCaL backend when
// XOLVER_HAS_CADICAL is defined, else a stub. These tests are written for
// the CaDiCaL path; stub-mode runs may show degraded behavior but should
// not crash. We assert the cross-backend minimal contract.

#include <doctest/doctest.h>
#include "contracts/SatSolver.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <algorithm>
#include <stdexcept>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <limits>
#include <map>
#include <utility>

using namespace xolver;

namespace {
struct ModelSourceHarness {
    struct Lookup : TheoryAtomLookup {
        std::vector<TheoryAtomRecord> atoms;
        const TheoryAtomRecord* findBySatVar(SatVar var) const override {
            for (const auto& atom : atoms) if (atom.satVar == var) return &atom;
            return nullptr;
        }
        std::vector<SatVar> allAtomVars() const override {
            std::vector<SatVar> result;
            for (const auto& atom : atoms) result.push_back(atom.satVar);
            return result;
        }
    } registry;
    struct Callbacks : TheoryPropagationCallbacks {
        std::map<SatVar, std::pair<bool, int>> sources;
        std::vector<std::pair<SatLit, int>> admitted;
        TheoryAssignmentView* view = nullptr;
        int backtracks = 0, fullChecks = 0;
        void assertTheoryLit(const TheoryAtomRecord&, SatLit literal, int level) override {
            sources[literal.var] = {literal.sign, level};
            admitted.emplace_back(literal, level);
        }
        void backtrackToLevel(int level) override {
            ++backtracks;
            for (auto it = sources.begin(); it != sources.end();)
                if (level == 0 || it->second.second > level) it = sources.erase(it);
                else ++it;
        }
        void setAssignmentView(TheoryAssignmentView* value) override { view = value; }
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort effort) override {
            CHECK(effort == TheoryEffort::Full);
            ++fullChecks;
            REQUIRE(view);
            for (const auto& [var, source] : sources)
                CHECK(view->value({var, source.first}) == LitValue::True);
            return TheoryCheckResult::consistent();
        }
    } theories;
    CadicalBackend backend;
    TheoryLemmaDatabase database;
    CadicalTheoryPropagator propagator{registry, theories, database, backend};
    ModelSourceHarness() { backend.connectPropagator(&propagator); }
    ~ModelSourceHarness() { backend.disconnectPropagator(); }
    SatVar boolean() {
        const auto var = backend.newVar();
        backend.addObservedVar(var);
        return var;
    }
    void registerAtom(SatVar var, TheoryId theory) {
        TheoryAtomPayload payload = theory == TheoryId::EUF
            ? TheoryAtomPayload(EufAtomPayload{NullExpr, NullExpr, Relation::Eq})
            : TheoryAtomPayload(LinearAtomPayload{{}, Relation::Eq, RealValue::fromInt(0)});
        registry.atoms.push_back({var, theory, false, NullExpr, std::move(payload)});
    }
    SatVar atom(TheoryId theory) {
        const auto var = boolean();
        registerAtom(var, theory);
        return var;
    }
};

struct ClauseDeliveryHarness {
    struct Lookup : TheoryAtomLookup {
        TheoryAtomRecord premise{};
        const TheoryAtomRecord* findBySatVar(SatVar var) const override {
            return var == premise.satVar ? &premise : nullptr;
        }
    } registry;
    struct Callbacks : TheoryPropagationCallbacks {
        std::optional<TheoryLemma> returned;
        std::vector<TheoryLemma> buffered;
        int checks = 0;
        void assertTheoryLit(const TheoryAtomRecord&, SatLit, int) override {}
        void backtrackToLevel(int) override {}
        void setAssignmentView(TheoryAssignmentView*) override {}
        TheoryCheckResult check(TheoryLemmaStorage& database, TheoryEffort) override {
            ++checks;
            if (returned) {
                (void)database.insertIfNew(*returned);
                return TheoryCheckResult::mkLemma(*returned);
            }
            return TheoryCheckResult::consistent();
        }
        std::vector<TheoryLemma> takeEntailmentPropagations() override {
            return std::exchange(buffered, {});
        }
    } theories;
    CadicalBackend backend;
    TheoryLemmaDatabase database;
    CadicalTheoryPropagator propagator{registry, theories, database, backend};
    SatVar premise, paddingA, paddingB, first, second;
    ClauseDeliveryHarness() {
        premise = backend.newVar();
        paddingA = backend.newVar();
        paddingB = backend.newVar();
        first = backend.newVar();
        second = backend.newVar();
        registry.premise = {premise, TheoryId::LRA, true, NullExpr,
            LinearAtomPayload{{}, Relation::Eq, RealValue::fromInt(0)}};
        backend.connectPropagator(&propagator);
        for (auto var : {premise, paddingA, paddingB, first, second})
            backend.addObservedVar(var);
    }
    ~ClauseDeliveryHarness() { backend.disconnectPropagator(); }
    TheoryLemma implication(SatVar consequent, LemmaKind kind = LemmaKind::Entailment) {
        return {{{premise, false}, {consequent, true}}, kind};
    }
    void checkPartial() {
        propagator.notify_assignment({static_cast<int>(premise),
            static_cast<int>(paddingA), static_cast<int>(paddingB)});
        CHECK(propagator.cb_propagate() == 0);
        REQUIRE(theories.checks == 1);
    }
};

struct SharedEqualityHarness {
    struct Registrar : DynamicAtomRegistrar {
        SatSolver& backend;
        explicit Registrar(SatSolver& solver) : backend(solver) {}
        SatLit registerDynamicAtom(ExprId, TheoryId) override {
            return SatLit::positive(backend.newVar());
        }
    };
    struct EqualityTheory : TheorySolver {
        TheoryId theory;
        std::vector<SharedEqualityPropagation> facts;
        explicit EqualityTheory(TheoryId id) : theory(id) {}
        TheoryId id() const override { return theory; }
        void push() override {}
        void pop(uint32_t) override {}
        void reset() override {}
        void backtrackToLevel(int) override {}
        void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
        bool supportsCombination() const override { return true; }
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
            return TheoryCheckResult::consistent();
        }
        std::vector<SharedEqualityPropagation> getDeducedSharedEqualities() override {
            return facts;
        }
    };
    CadicalBackend backend;
    Registrar registrar{backend};
    TheoryAtomRegistry registry;
    TheoryManager manager;
    TheoryLemmaDatabase database;
    CadicalTheoryPropagator propagator{registry, manager, database, backend};
    EqualityTheory* theory;

    explicit SharedEqualityHarness(TheoryId id) {
        registry.setContext(&backend, &registrar);
        manager.setCombinationMode(true);
        manager.setRegistry(&registry);
        auto solver = std::make_unique<EqualityTheory>(id);
        theory = solver.get();
        manager.registerSolver(std::move(solver));
        backend.connectPropagator(&propagator);
    }
    ~SharedEqualityHarness() { backend.disconnectPropagator(); }

    std::vector<TheoryLemma> drain() {
        std::vector<TheoryLemma> clauses;
        for (size_t i = 0; i < 256; ++i) {
            auto result = manager.check(database, TheoryEffort::Full);
            if (result.kind == TheoryCheckResult::Kind::Consistent) return clauses;
            REQUIRE(result.lemmaOpt);
            clauses.push_back(*result.lemmaOpt);
            database.markInstalled(clauses.back());
        }
        FAIL("Shared equality publication did not finish");
        return clauses;
    }
};
} // namespace

TEST_CASE("SAT sharing: dense proved equalities publish a connected linear basis") {
    for (const auto id : {TheoryId::LIA, TheoryId::LRA, TheoryId::EUF}) {
        CAPTURE(static_cast<int>(id));
        SharedEqualityHarness h(id);
        const SatLit premise = SatLit::positive(h.backend.newVar());
        constexpr SharedTermId count = 16;
        for (SharedTermId a = 0; a < count; ++a)
            for (SharedTermId b = a + 1; b < count; ++b)
                h.theory->facts.push_back({a, b, {premise}});
        const auto clauses = h.drain();
        CHECK(clauses.size() == count - 1);
        CHECK(h.registry.numAtomVars() == count - 1);
        std::vector<std::pair<SharedTermId, SharedTermId>> edges;
        for (const auto& clause : clauses) {
            REQUIRE(clause.lits.size() == 2);
            CHECK(clause.lits.front() == premise.negated());
            const auto* record = h.registry.findBySatVar(clause.lits.back().var);
            REQUIRE(record);
            const auto& edge = std::get<SharedEqualityPayload>(record->payload);
            edges.emplace_back(edge.a, edge.b);
        }
        std::vector<bool> reached(count, false);
        reached.front() = true;
        for (SharedTermId pass = 0; pass < count; ++pass) {
            for (const auto& [a, b] : edges)
                if (reached[a] || reached[b]) reached[a] = reached[b] = true;
        }
        CHECK(std::all_of(reached.begin(), reached.end(), [](bool value) { return value; }));
    }
}

TEST_CASE("SAT sharing: basis explanations refresh after backtracking") {
    SharedEqualityHarness h(TheoryId::LRA);
    const SatLit first = SatLit::positive(h.backend.newVar());
    const SatLit second = SatLit::positive(h.backend.newVar());
    h.theory->facts = {{1, 2, {first}}, {2, 3, {first}}, {1, 3, {first}}, {7, 8, {second}}};
    const auto initial = h.drain();
    CHECK(initial.size() == 3);
    CHECK(h.registry.numAtomVars() == 3);
    h.manager.backtrackToLevel(0);
    for (auto& fact : h.theory->facts) fact.reasons = {second};
    const auto refreshed = h.drain();
    REQUIRE(refreshed.size() == 2);
    for (const auto& clause : refreshed) {
        REQUIRE(clause.lits.size() == 2);
        CHECK(clause.lits.front() == second.negated());
        CHECK(std::find(clause.lits.begin(), clause.lits.end(), first.negated()) == clause.lits.end());
    }
    CHECK(h.registry.numAtomVars() == 3);
}

TEST_CASE("SAT delivery: partial checks install entailments but retain speculative guesses") {
    for (const auto kind : {LemmaKind::Entailment, LemmaKind::Guess}) {
        ClauseDeliveryHarness h;
        const auto clause = h.implication(h.first, kind);
        h.theories.returned = clause;
        h.checkPartial();
        bool forgettable = true;
        CHECK_FALSE(h.database.isInstalled(clause));
        if (kind == LemmaKind::Guess) {
            CHECK_FALSE(h.propagator.cb_has_external_clause(forgettable));
            continue;
        }
        REQUIRE(h.propagator.cb_has_external_clause(forgettable));
        CHECK_FALSE(forgettable);
        CHECK(h.propagator.cb_add_external_clause_lit() == -static_cast<int>(h.premise));
        CHECK(h.propagator.cb_add_external_clause_lit() == static_cast<int>(h.first));
        CHECK_FALSE(h.database.isInstalled(clause));
        CHECK(h.propagator.cb_add_external_clause_lit() == 0);
        CHECK(h.database.isInstalled(clause));
        CHECK_FALSE(h.propagator.cb_has_external_clause(forgettable));
    }
}

TEST_CASE("SAT delivery: queued clauses retain individual boundaries and acknowledgments") {
    ClauseDeliveryHarness h;
    const auto first = h.implication(h.first);
    const auto second = h.implication(h.second);
    h.theories.buffered = {first, second};
    h.checkPartial();
    bool forgettable = true;
    REQUIRE(h.propagator.cb_has_external_clause(forgettable));
    CHECK(h.propagator.cb_add_external_clause_lit() == -static_cast<int>(h.premise));
    CHECK(h.propagator.cb_add_external_clause_lit() == static_cast<int>(h.first));
    CHECK_FALSE(h.database.isInstalled(first));
    CHECK(h.propagator.cb_has_external_clause(forgettable));
    CHECK_FALSE(h.database.isInstalled(first));
    CHECK(h.propagator.cb_add_external_clause_lit() == 0);
    CHECK(h.database.isInstalled(first));
    CHECK_FALSE(h.database.isInstalled(second));
    REQUIRE(h.propagator.cb_has_external_clause(forgettable));
    CHECK(h.propagator.cb_add_external_clause_lit() == -static_cast<int>(h.premise));
    CHECK(h.propagator.cb_add_external_clause_lit() == static_cast<int>(h.second));
    CHECK(h.propagator.cb_add_external_clause_lit() == 0);
    CHECK(h.database.isInstalled(second));
    CHECK_FALSE(h.propagator.cb_has_external_clause(forgettable));
}

TEST_CASE("SAT delivery: shared equalities remain deliverable until installation") {
    struct Registrar : DynamicAtomRegistrar {
        SatSolver& backend;
        explicit Registrar(SatSolver& solver) : backend(solver) {}
        SatLit registerDynamicAtom(ExprId, TheoryId) override {
            return SatLit::positive(backend.newVar());
        }
    };
    struct EqualityTheory : TheorySolver {
        SatLit reason;
        explicit EqualityTheory(SatLit premise) : reason(premise) {}
        TheoryId id() const override { return TheoryId::LRA; }
        void push() override {}
        void pop(uint32_t) override {}
        void reset() override {}
        void backtrackToLevel(int) override {}
        void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
        bool supportsCombination() const override { return true; }
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
            return TheoryCheckResult::consistent();
        }
        std::vector<SharedEqualityPropagation> getDeducedSharedEqualities() override {
            return {{1, 2, {reason}}};
        }
    };
    CadicalBackend backend;
    Registrar registrar{backend};
    const auto premise = SatLit::positive(backend.newVar());
    TheoryAtomRegistry registry;
    registry.setContext(&backend, &registrar);
    TheoryManager manager;
    manager.setCombinationMode(true);
    manager.setRegistry(&registry);
    manager.registerSolver(std::make_unique<EqualityTheory>(premise));
    TheoryLemmaDatabase database;
    CadicalTheoryPropagator propagator{registry, manager, database, backend};
    backend.connectPropagator(&propagator);
    struct Disconnect {
        CadicalBackend& backend;
        ~Disconnect() { backend.disconnectPropagator(); }
    } disconnect{backend};
    const auto first = manager.check(database, TheoryEffort::Standard);
    REQUIRE(first.lemmaOpt);
    CHECK(first.lemmaOpt->kind == LemmaKind::Entailment);
    CHECK_FALSE(database.isInstalled(*first.lemmaOpt));
    const auto retry = manager.check(database, TheoryEffort::Full);
    REQUIRE(retry.lemmaOpt);
    CHECK(retry.lemmaOpt->lits == first.lemmaOpt->lits);
    database.markInstalled(*retry.lemmaOpt);
    CHECK(manager.check(database, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
}

TEST_CASE("Model sources: fully observed models retain the incremental theory prefix") {
    ModelSourceHarness h;
    const auto p = h.atom(TheoryId::LRA), q = h.atom(TheoryId::EUF), r = h.boolean();
    h.propagator.notify_assignment({static_cast<int>(p)});
    h.propagator.notify_new_decision_level();
    h.propagator.notify_assignment({-static_cast<int>(q)});
    REQUIRE(h.theories.admitted.size() == 2);
    CHECK(h.propagator.cb_check_found_model({-static_cast<int>(q), static_cast<int>(r), static_cast<int>(p)}));
    CHECK(h.propagator.cb_check_found_model({static_cast<int>(p), -static_cast<int>(r), -static_cast<int>(q)}));
    CHECK(h.theories.admitted.size() == 2);
    CHECK(h.theories.backtracks == 0);
    CHECK(h.theories.fullChecks == 2);
    CHECK(h.theories.sources.at(p).second == 0);
    CHECK(h.theories.sources.at(q).second == 1);
    h.propagator.notify_backtrack(0);
    REQUIRE(h.theories.sources.size() == 1);
    CHECK(h.theories.sources.at(p).first);
    h.propagator.notify_new_decision_level();
    h.propagator.notify_assignment({static_cast<int>(q)});
    CHECK(h.propagator.cb_check_found_model({static_cast<int>(p), static_cast<int>(q), -static_cast<int>(r)}));
    CHECK(h.theories.admitted.size() == 4); // root restoration and the changed decision
    CHECK(h.theories.backtracks == 1);
    CHECK(h.theories.fullChecks == 3);
    CHECK(h.theories.sources.at(q).first);
}

TEST_CASE("Model sources: incomplete observations rebuild at the real source levels") {
    ModelSourceHarness h;
    const auto p = h.atom(TheoryId::LIA), q = h.atom(TheoryId::LRA), r = h.boolean();
    h.propagator.notify_new_decision_level();
    h.propagator.notify_new_decision_level();
    h.propagator.notify_assignment({static_cast<int>(p)});
    CHECK(h.propagator.cb_check_found_model({static_cast<int>(p), static_cast<int>(r), -static_cast<int>(q)}));
    REQUIRE(h.theories.admitted.size() == 3);
    CHECK(h.theories.admitted[1].first.var == q);
    CHECK(h.theories.admitted[1].second == 0);
    CHECK(h.theories.admitted[2].first.var == p);
    CHECK(h.theories.admitted[2].second == 2);
    CHECK(h.theories.backtracks == 1);
    CHECK(h.propagator.cb_check_found_model({-static_cast<int>(q), -static_cast<int>(r), static_cast<int>(p)}));
    CHECK(h.theories.admitted.size() == 5);
    CHECK(h.theories.backtracks == 2);
    CHECK(h.propagator.cb_check_found_model({-static_cast<int>(p), static_cast<int>(q), static_cast<int>(r)}));
    CHECK_FALSE(h.theories.sources.at(p).first);
    CHECK(h.theories.sources.at(p).second == 2);
    CHECK(h.theories.sources.at(q).first);
    CHECK(h.theories.fullChecks == 3);
}

TEST_CASE("Model sources: registration growth and truncated models require complete admission") {
    ModelSourceHarness h;
    const auto p = h.atom(TheoryId::LRA), q = h.boolean();
    SUBCASE("a previous Boolean notification did not admit a later theory atom") {
        h.propagator.notify_assignment({static_cast<int>(p), static_cast<int>(q)});
        h.registerAtom(q, TheoryId::EUF);
        CHECK(h.propagator.cb_check_found_model({static_cast<int>(p), static_cast<int>(q)}));
        REQUIRE(h.theories.sources.size() == 2);
        CHECK(h.theories.sources.at(q).first);
        CHECK(h.theories.backtracks == 1);
    }
    SUBCASE("a missing observed source cannot remain in a truncated model") {
        h.registerAtom(q, TheoryId::LIA);
        h.propagator.notify_assignment({static_cast<int>(p), -static_cast<int>(q)});
        CHECK(h.propagator.cb_check_found_model({static_cast<int>(p)}));
        CHECK(h.theories.sources.size() == 1);
        CHECK_FALSE(h.theories.sources.contains(q));
        CHECK(h.theories.backtracks == 1);
    }
}

TEST_CASE("SAT: theory model decisions include atoms registered after the first request") {
    struct Lookup : TheoryAtomLookup {
        std::vector<TheoryAtomRecord> atoms;
        const TheoryAtomRecord* findBySatVar(SatVar var) const override {
            for (const auto& atom : atoms) if (atom.satVar == var) return &atom;
            return nullptr;
        }
        std::vector<SatVar> allAtomVars() const override {
            std::vector<SatVar> result;
            for (const auto& atom : atoms) result.push_back(atom.satVar);
            return result;
        }
    } registry;
    struct Callbacks : TheoryPropagationCallbacks {
        int evaluations = 0;
        SatVar negative = 0;
        void assertTheoryLit(const TheoryAtomRecord&, SatLit, int) override {}
        void backtrackToLevel(int) override {}
        void setAssignmentView(TheoryAssignmentView*) override {}
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
            return TheoryCheckResult::consistent();
        }
        std::optional<bool> evalTheoryAtom(SatVar var) override {
            ++evaluations;
            return var != negative;
        }
    } theories;
    struct Selection : Propagator {
        DecisionSource source = DecisionSource::SatActivity;
        int pick = 0;
        int decide() override { return pick; }
        DecisionSource decisionSource(const DecisionContext&) override { return source; }
    } selection;
    CadicalBackend backend;
    TheoryLemmaDatabase lemmas;
    CadicalTheoryPropagator propagator{registry, theories, lemmas, backend};
    backend.connectPropagator(&propagator);
    struct Disconnect {
        CadicalBackend& backend;
        ~Disconnect() { backend.disconnectPropagator(); }
    } disconnect{backend};
    CHECK(propagator.cb_decide() == 0); // initialize an empty candidate snapshot
    const auto nonLinear = backend.newVar();
    registry.atoms.push_back({nonLinear, TheoryId::EUF, false, NullExpr,
                             EufAtomPayload{NullExpr, NullExpr, Relation::Eq}});
    backend.addObservedVar(nonLinear);
    CHECK(propagator.cb_decide() == 0); // registry size is not the linear count
    const auto real = backend.newVar();
    registry.atoms.push_back({real, TheoryId::LRA, true, NullExpr,
                             LinearAtomPayload{{}, Relation::Eq, RealValue::fromInt(0)}});
    backend.addObservedVar(real);
    CHECK(propagator.cb_decide() == static_cast<int>(real));
    propagator.notify_assignment({static_cast<int>(real)});
    propagator.setUserPropagator(&selection);
    const auto integer = backend.newVar();
    registry.atoms.push_back({integer, TheoryId::LIA, true, NullExpr,
                             LinearAtomPayload{{}, Relation::Lt, RealValue::fromInt(0)}});
    backend.addObservedVar(integer);
    CHECK(registry.numAtomVars() == 3);
    CHECK((registry.linearAtomVars(1) == std::vector<SatVar>{real, integer}));
    CHECK((registry.linearAtomVars(2) == std::vector<SatVar>{integer}));
    CHECK(registry.linearAtomVars(3).empty());
    theories.negative = integer;
    const auto previousEvaluations = theories.evaluations;
    CHECK(propagator.cb_decide() == 0);
    CHECK(theories.evaluations == previousEvaluations);
    selection.source = DecisionSource::TheoryModel;
    CHECK(propagator.cb_decide() == -static_cast<int>(integer));
    selection.pick = static_cast<int>(integer);
    CHECK(propagator.cb_decide() == selection.pick); // explicit choice wins
    selection.pick = 0;
    propagator.notify_new_decision_level();
    propagator.notify_assignment({-static_cast<int>(integer)});
    CHECK(propagator.cb_decide() == 0); // assigned atoms are never proposed
    propagator.notify_backtrack(0);
    CHECK(propagator.cb_decide() == -static_cast<int>(integer));
}

TEST_CASE("SAT: decision sources preserve explicit steering and mandatory model checks") {
    struct Lookup : TheoryAtomLookup {
        TheoryAtomRecord atom{};
        const TheoryAtomRecord* findBySatVar(SatVar v) const override {
            return v == atom.satVar ? &atom : nullptr;
        }
        std::vector<SatVar> allAtomVars() const override { return {atom.satVar}; }
    } registry;
    struct Callbacks : TheoryPropagationCallbacks {
        TheoryAssignmentView* view = nullptr;
        SatVar truth = 0;
        int evaluations = 0, fullChecks = 0;
        void assertTheoryLit(const TheoryAtomRecord&, SatLit, int) override {}
        void backtrackToLevel(int) override {}
        void setAssignmentView(TheoryAssignmentView* v) override { view = v; }
        std::optional<bool> evalTheoryAtom(SatVar) override { ++evaluations; return true; }
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort effort) override {
            if (effort == TheoryEffort::Full) {
                ++fullChecks;
                if (!view || view->value(SatLit::positive(truth)) != LitValue::True)
                    return TheoryCheckResult::mkLemma(TheoryLemma{{SatLit::positive(truth)}});
            }
            return TheoryCheckResult::consistent();
        }
    } theories;
    struct Selection : Propagator {
        DecisionSource source = DecisionSource::TheoryModel;
        DecisionContext last;
        int pick = 0, sourceCalls = 0;
        int decide() override { return pick; }
        DecisionSource decisionSource(const DecisionContext& c) override {
            last = c; ++sourceCalls; return source;
        }
    } selection;
    TheoryLemmaDatabase lemmas;
    CadicalBackend backend;
    const auto p = backend.newVar(), q = backend.newVar(), r = backend.newVar();
    registry.atom.satVar = p;
    registry.atom.theory = TheoryId::LRA;
    // p represents the valid arithmetic atom 0 = 0.
    registry.atom.payload = LinearAtomPayload{{}, Relation::Eq, RealValue::fromInt(0)};
    theories.truth = p;
    CadicalTheoryPropagator propagator{registry, theories, lemmas, backend};
    backend.connectPropagator(&propagator);
    struct Disconnect {
        CadicalBackend& backend;
        ~Disconnect() { backend.disconnectPropagator(); }
    } disconnect{backend};
    backend.addObservedVar(p);
    backend.addObservedVar(q);

    SUBCASE("default, native SAT, explicit choices, and backtracking") {
        CHECK(propagator.cb_decide() == static_cast<int>(p));
        propagator.setUserPropagator(&selection);
        CHECK(propagator.cb_decide() == static_cast<int>(p));
        const auto previousEvaluations = theories.evaluations;
        selection.source = DecisionSource::SatActivity;
        propagator.notify_new_decision_level();
        CHECK(propagator.cb_decide() == 0);
        CHECK(theories.evaluations == previousEvaluations);
        CHECK(selection.last.level == 1);
        CHECK(selection.last.requests == 3);
        selection.pick = -static_cast<int>(q);
        const auto previousSourceCalls = selection.sourceCalls;
        CHECK(propagator.cb_decide() == selection.pick);
        CHECK(selection.sourceCalls == previousSourceCalls);
        propagator.notify_assignment({selection.pick});
        CHECK(propagator.cb_decide() == 0); // already assigned explicit pick
        propagator.notify_backtrack(0);
        CHECK(propagator.cb_decide() == selection.pick);
        selection.pick = std::numeric_limits<int>::min();
        CHECK(propagator.cb_decide() == 0); // cannot negate INT_MIN
    }
    SUBCASE("native SAT still rejects theory-invalid complete models") {
        selection.source = DecisionSource::SatActivity;
        propagator.setUserPropagator(&selection);
        backend.addClause({SatLit::positive(q), SatLit::positive(r)});
        backend.setDefaultPhase(p, false);
        backend.setDeadline(std::chrono::steady_clock::now() + std::chrono::seconds(5));
        REQUIRE((backend.solve() == SatSolver::SolveResult::Sat));
        CHECK(backend.value(p));
        CHECK(theories.fullChecks > 0);
    }
}

#ifdef XOLVER_ENABLE_PROOFS
TEST_CASE("SAT: preprocessing theory clauses remain explicit proof assumptions") {
    const auto base = (std::filesystem::temp_directory_path() / "xolver-theory-base-proof").string();
    {
        CadicalBackend solver;
        REQUIRE(solver.enableProofTrace(base, false));
        const auto p = solver.newVar(), q = solver.newVar();
        solver.addClause({SatLit::positive(p)});
        solver.addClause({SatLit::negative(q)});
        // Interpret p as x<=0 and q as x<=1: p implies q is a theory axiom,
        // not a Boolean tautology or an original assertion.
        solver.addTheoryClause({SatLit::negative(p), SatLit::positive(q)});
        REQUIRE((solver.solve() == SatSolver::SolveResult::Unsat));
        solver.finalizeProof();
    }
    std::ifstream input(base + ".cnf");
    const std::string contents((std::istreambuf_iterator<char>(input)), {});
    CHECK(contents.find("2 original clauses, 1 theory lemmas assumed") != std::string::npos);
    std::filesystem::remove(base + ".cnf");
    std::filesystem::remove(base + ".drat");
}
#endif

TEST_CASE("SAT: external variable allocation has no phantom decision domain") {
    CadicalBackend solver;
    std::vector<SatVar> variables;
    for (int i = 0; i < 32; ++i) {
        variables.push_back(solver.newVar());
        CHECK(solver.getStats().vars <= i + 1);
    }
    auto p = variables.front();
    solver.addClause({SatLit::positive(p)});
    REQUIRE((solver.solve() == SatSolver::SolveResult::Sat));
    auto fresh = solver.newVar();
    CHECK(std::find(variables.begin(), variables.end(), fresh) == variables.end());
    solver.addClause({SatLit::negative(fresh), SatLit::negative(p)});
    REQUIRE((solver.solve({SatLit::positive(fresh)}) == SatSolver::SolveResult::Unsat));
    REQUIRE((solver.solve({SatLit::negative(fresh)}) == SatSolver::SolveResult::Sat));
    CHECK(solver.value(p));
    CHECK_FALSE(solver.value(fresh));
}

TEST_CASE("SAT: expired local deadline consumes assumptions and permits reuse") {
    auto s = createSatSolver();
    const auto p = s->newVar();
    s->addClause({SatLit::positive(p)});
    s->setDeadline(std::chrono::steady_clock::now());
    CHECK((s->solve({SatLit::negative(p)}) == SatSolver::SolveResult::Unknown));
    s->setDeadline(std::chrono::steady_clock::time_point::max());
    CHECK((s->solve() == SatSolver::SolveResult::Sat));
    CHECK(s->value(p));
}

TEST_CASE("SAT: local deadline interrupts an internal pigeonhole search") {
    auto s = createSatSolver();
    constexpr int pigeons = 16, holes = 15;
    SatVar vars[pigeons][holes];
    for (auto& row : vars) {
        std::vector<SatLit> clause;
        for (auto& v : row) { v = s->newVar(); clause.push_back(SatLit::positive(v)); }
        s->addClause(clause);
    }
    for (int h = 0; h < holes; ++h)
        for (int a = 0; a < pigeons; ++a)
            for (int b = a + 1; b < pigeons; ++b)
                s->addClause({SatLit::negative(vars[a][h]), SatLit::negative(vars[b][h])});
    const auto start = std::chrono::steady_clock::now();
    s->setDeadline(start + std::chrono::milliseconds(20));
    const auto result = s->solve();
    CHECK((result != SatSolver::SolveResult::Sat));
    CHECK((std::chrono::steady_clock::now() - start < std::chrono::seconds(5)));
}

TEST_CASE("SAT: empty solver returns sat") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto r = s->solve();
    // No clauses ⇒ trivially sat.
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
}

TEST_CASE("SAT: single unit clause is sat") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto v = s->newVar();
    s->addClause({SatLit::positive(v)});
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(s->value(v) == true);
}

TEST_CASE("SAT: complementary unit clauses are unsat") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto v = s->newVar();
    s->addClause({SatLit::positive(v)});
    s->addClause({SatLit::negative(v)});
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("SAT: chain forces unit propagation") {
    // p, !p ∨ q, !q ∨ r, !r ∨ s — forces p=q=r=s=true.
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar(); auto q = s->newVar();
    auto r = s->newVar(); auto t = s->newVar();
    s->addClause({SatLit::positive(p)});
    s->addClause({SatLit::negative(p), SatLit::positive(q)});
    s->addClause({SatLit::negative(q), SatLit::positive(r)});
    s->addClause({SatLit::negative(r), SatLit::positive(t)});
    auto res = s->solve();
    CHECK(static_cast<int>(res) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(s->value(p) == true);
    CHECK(s->value(q) == true);
    CHECK(s->value(r) == true);
    CHECK(s->value(t) == true);
}

TEST_CASE("SAT: 2-clause 3-CNF unsat (small pigeonhole)") {
    // (p ∨ q) ∧ (!p ∨ q) ∧ (p ∨ !q) ∧ (!p ∨ !q) — unsat.
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar(), q = s->newVar();
    s->addClause({SatLit::positive(p), SatLit::positive(q)});
    s->addClause({SatLit::negative(p), SatLit::positive(q)});
    s->addClause({SatLit::positive(p), SatLit::negative(q)});
    s->addClause({SatLit::negative(p), SatLit::negative(q)});
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("SAT: assumption forces a value") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar(), q = s->newVar();
    // (p ∨ q) — sat both ways; force !p by assumption.
    s->addClause({SatLit::positive(p), SatLit::positive(q)});
    auto r = s->solve({SatLit::negative(p)});
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(s->value(p) == false);
    CHECK(s->value(q) == true);
}

TEST_CASE("SAT: contradicting assumption gives unsat") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar();
    s->addClause({SatLit::positive(p)});
    auto r = s->solve({SatLit::negative(p)});
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("SAT: failed assumption appears in unsat core (if backend supports)") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar();
    s->addClause({SatLit::positive(p)});
    auto neg_p = SatLit::negative(p);
    auto r = s->solve({neg_p});
    REQUIRE(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Unsat));
    auto core = s->getFailedAssumptions();
    // CaDiCaL returns the failed assumption; stub may return empty.
    if (!core.empty()) {
        bool found = false;
        for (auto a : core) {
            if (a == neg_p) { found = true; break; }
        }
        CHECK(found);
    }
}

TEST_CASE("SAT: incremental solve — second call sees both clauses") {
    auto s = createSatSolver();
    REQUIRE(s);
    auto p = s->newVar();
    s->addClause({SatLit::positive(p)});
    auto r1 = s->solve();
    CHECK(static_cast<int>(r1) == static_cast<int>(SatSolver::SolveResult::Sat));
    s->addClause({SatLit::negative(p)});  // now contradictory
    auto r2 = s->solve();
    CHECK(static_cast<int>(r2) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("SAT: many variables one large clause") {
    auto s = createSatSolver();
    REQUIRE(s);
    std::vector<SatLit> clause;
    for (int i = 0; i < 100; ++i) {
        clause.push_back(SatLit::positive(s->newVar()));
    }
    s->addClause(clause);
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
    // At least one of the 100 vars must be true.
    bool any_true = false;
    for (auto lit : clause) {
        if (s->value(lit.var)) { any_true = true; break; }
    }
    CHECK(any_true);
}

TEST_CASE("SAT: addObservedVar requires ExternalPropagator setup") {
    // Invalid setup must fail at our boundary, without aborting the process.
    auto s = createSatSolver();
    REQUIRE(s);
    auto v = s->newVar();
    CHECK_THROWS_AS(s->addObservedVar(v), std::logic_error);
    s->addClause({SatLit::positive(v)});
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
}

TEST_CASE("SAT: retained root assertions remain available after a root backtrack") {
    for (const bool integer : {false, true}) {
        for (const bool negativeRoot : {false, true}) {
            CAPTURE(integer);
            CAPTURE(negativeRoot);
            CadicalBackend backend;
            TheoryAtomRegistry registry;
            registry.setContext(&backend, nullptr);
            TheoryManager manager;
            TheoryLemmaDatabase lemmas;
            const auto theory = integer ? TheoryId::LIA : TheoryId::LRA;
            if (integer) {
                auto solver = std::make_unique<LiaSolver>();
                solver->setRegistry(&registry);
                manager.registerSolver(std::move(solver));
            } else {
                auto solver = std::make_unique<LraSolver>();
                solver->setRegistry(&registry);
                manager.registerSolver(std::move(solver));
            }
            CadicalTheoryPropagator propagator{registry, manager, lemmas, backend};
            backend.connectPropagator(&propagator);
            struct Disconnect {
                CadicalBackend& backend;
                ~Disconnect() { backend.disconnectPropagator(); }
            } disconnect{backend};
            auto atom = [&](LinearFormKey form, Relation relation, mpq_class bound) {
                auto var = backend.newVar();
                registry.registerParsedTheoryAtom(var, static_cast<ExprId>(var), theory,
                    LinearAtomPayload{form, relation, RealValue::fromMpq(bound)});
                return static_cast<int>(var);
            };
            // Either signed literal states x >= 1.
            const int rootAtom = atom({{{"x", 1}}}, negativeRoot ? Relation::Lt : Relation::Geq, 1);
            const int root = negativeRoot ? -rootAtom : rootAtom;
            const int harmless = atom({{{"z", 1}}}, Relation::Geq, 0);
            const int link = atom({{{"x", 1}, {"y", -1}}}, Relation::Leq, 0);
            const int upper = atom({{{"y", 1}}}, Relation::Lt, 1);
            const int lower = atom({{{"y", 1}}}, Relation::Geq, 1);
            propagator.notify_assignment({root});
            REQUIRE(manager.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            propagator.notify_new_decision_level();
            propagator.notify_assignment({harmless});
            REQUIRE(manager.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
            propagator.notify_backtrack(0);
            propagator.notify_new_decision_level();
            propagator.notify_assignment({link, upper});
            auto conflict = manager.check(lemmas, TheoryEffort::Standard);
            CHECK(conflict.kind == TheoryCheckResult::Kind::Conflict);
            if (conflict.conflictOpt) {
                const auto& reasons = conflict.conflictOpt->clause;
                CHECK(std::find(reasons.begin(), reasons.end(), SatLit{static_cast<SatVar>(rootAtom), negativeRoot}) != reasons.end());
                CHECK(std::find(reasons.begin(), reasons.end(), SatLit::negative(static_cast<SatVar>(harmless))) == reasons.end());
                CHECK(reasons.size() == 3);
                CHECK(std::find(reasons.begin(), reasons.end(), SatLit::negative(static_cast<SatVar>(link))) != reasons.end());
                CHECK(std::find(reasons.begin(), reasons.end(), SatLit::negative(static_cast<SatVar>(upper))) != reasons.end());
            }
            // Discard the incompatible branch, retain x >= 1, and reuse state.
            propagator.notify_backtrack(0);
            propagator.notify_new_decision_level();
            propagator.notify_assignment({link, lower});
            CHECK(manager.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
        }
    }
}

TEST_CASE("SAT: restoring retained roots does not readmit a preserving theory's assertions") {
    struct PreservingTheory : TheorySolver {
        int admissions = 0;
        std::vector<std::pair<int, SatLit>> active;
        TheoryId id() const override { return TheoryId::EUF; }
        void push() override {}
        void pop(uint32_t) override {}
        void reset() override { active.clear(); }
        void assertLit(const TheoryAtomRecord&, bool, int level, SatLit lit) override {
            ++admissions;
            active.emplace_back(level, lit);
        }
        void backtrackToLevel(int level) override {
            std::erase_if(active, [level](const auto& entry) { return entry.first > level; });
        }
        TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
            return TheoryCheckResult::consistent();
        }
    };
    CadicalBackend backend;
    TheoryAtomRegistry registry;
    registry.setContext(&backend, nullptr);
    TheoryManager manager;
    TheoryLemmaDatabase lemmas;
    auto theory = std::make_unique<PreservingTheory>();
    auto* retained = theory.get();
    manager.registerSolver(std::move(theory));
    CadicalTheoryPropagator propagator{registry, manager, lemmas, backend};
    backend.connectPropagator(&propagator);
    struct Disconnect {
        CadicalBackend& backend;
        ~Disconnect() { backend.disconnectPropagator(); }
    } disconnect{backend};
    const auto root = backend.newVar(), branch = backend.newVar();
    for (const auto var : {root, branch})
        registry.registerParsedTheoryAtom(var, NullExpr, TheoryId::EUF,
            EufAtomPayload{NullExpr, NullExpr, Relation::Eq});
    propagator.notify_assignment({-static_cast<int>(root)});
    for (int repeat = 0; repeat < 32; ++repeat) {
        propagator.notify_new_decision_level();
        propagator.notify_assignment({static_cast<int>(branch)});
        propagator.notify_backtrack(0);
        REQUIRE(retained->active.size() == 1);
        CHECK(retained->active.front().first == 0);
        CHECK(retained->active.front().second == SatLit::negative(root));
        CHECK(retained->admissions == repeat + 2);
    }
}

TEST_CASE("Arithmetic: root reconstruction keeps its explicit clear and restore semantics") {
    for (const bool integer : {false, true}) {
        std::unique_ptr<TheorySolver> solver;
        if (integer) solver = std::make_unique<LiaSolver>();
        else solver = std::make_unique<LraSolver>();
        TheoryLemmaDatabase lemmas;
        const TheoryAtomRecord root{1, solver->id(), false, NullExpr,
            LinearAtomPayload{{{{"x", 1}}}, Relation::Geq, RealValue::fromInt(1)}};
        const TheoryAtomRecord upper{2, solver->id(), false, NullExpr,
            LinearAtomPayload{{{{"x", 1}}}, Relation::Lt, RealValue::fromInt(1)}};
        solver->assertLit(root, true, 0, SatLit::positive(1));
        REQUIRE(solver->check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        solver->backtrackToLevel(0);
        solver->assertLit(upper, true, 0, SatLit::positive(2));
        CHECK(solver->check(lemmas).kind == TheoryCheckResult::Kind::Consistent);
        solver->restoreRootLiteral(root, true, SatLit::positive(1));
        CHECK(solver->check(lemmas).kind == TheoryCheckResult::Kind::Conflict);
    }
}
