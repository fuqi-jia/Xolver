// White-box: SatSolver (CaDiCaL backend) — interface compliance and corner
// cases that downstream theories implicitly rely on (unit propagation,
// assumption-based unsat core, empty clause, single-literal clauses, etc.).
//
// Note: the createSatSolver() factory returns the CaDiCaL backend when
// XOLVER_HAS_CADICAL is defined, else a stub. These tests are written for
// the CaDiCaL path; stub-mode runs may show degraded behavior but should
// not crash. We assert the cross-backend minimal contract.

#include <doctest/doctest.h>
#include "sat/SatSolver.h"

using namespace xolver;

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

TEST_CASE("SAT: addObservedVar requires ExternalPropagator setup" * doctest::skip()) {
    // Skipped: CaDiCaL aborts when addObservedVar is called without an
    // associated ExternalPropagator. This is expected backend behavior, not
    // a bug — but means we can't test the API standalone here. Real coverage
    // happens via CadicalTheoryPropagator integration tests.
    auto s = createSatSolver();
    REQUIRE(s);
    auto v = s->newVar();
    s->addObservedVar(v);
    s->addClause({SatLit::positive(v)});
    auto r = s->solve();
    CHECK(static_cast<int>(r) == static_cast<int>(SatSolver::SolveResult::Sat));
}
