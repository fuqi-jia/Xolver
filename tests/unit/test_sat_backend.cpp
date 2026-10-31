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

using namespace xolver;

TEST_CASE("SAT: decision sources preserve explicit steering and mandatory model checks") {
    struct Lookup : TheoryAtomLookup {
        TheoryAtomRecord atom{};
        const TheoryAtomRecord* findBySatVar(SatVar v) const override {
            return v == atom.satVar ? &atom : nullptr;
        }
        std::vector<SatVar> linearAtomVars() const override { return {atom.satVar}; }
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
