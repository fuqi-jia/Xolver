#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>

using namespace xolver;
using Eager = bitblast::EagerBitBlastSolver;

namespace {
// Inject a deterministic scheduling yield, with the actual clauses and SAT
// backend intact. Tests do not depend on a tiny wall-clock allocation.
struct YieldingSat final : SatSolver {
    std::unique_ptr<SatSolver> backend = createSatSolver();
    unsigned& allocations;
    unsigned& clauses;
    bool yielded = false;
    YieldingSat(unsigned& allocations, unsigned& clauses)
        : allocations(allocations), clauses(clauses) { ++allocations; }
    SatVar newVar() override { return backend->newVar(); }
    void addClause(const std::vector<SatLit>& clause) override {
        ++clauses;
        backend->addClause(clause);
    }
    SolveResult solve() override { return solve({}); }
    SolveResult solve(const std::vector<SatLit>& assumptions) override {
        if (!yielded) { yielded = true; return SolveResult::Unknown; }
        return backend->solve(assumptions);
    }
    bool value(SatVar variable) const override { return backend->value(variable); }
    bool limit(const char* name, int count) override { return backend->limit(name, count); }
    void setDeadline(std::chrono::steady_clock::time_point deadline) override {
        backend->setDeadline(deadline);
    }
    void setProgressCallback(std::function<bool()> callback) override {
        backend->setProgressCallback(std::move(callback));
    }
};

struct Query {
    NativeTerms terms;
    SortId number;
    ExprId x, p;
    explicit Query(bool real = false) : number(real ? 2 : 1) {
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        terms.registerSort(2, SortKind::Real);
        terms.setBoolSortId(0);
        terms.setIntSortId(1);
        terms.setRealSortId(2);
        x = terms.add({Kind::Variable, number, {}, Payload(std::string("x"))});
        p = terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
    }
    ExprId constant(int value) {
        return terms.add({number == 1 ? Kind::ConstInt : Kind::ConstReal,
                          number, {}, Payload(std::to_string(value))});
    }
    ExprId predicate(Kind kind, ExprId a, ExprId b) {
        return terms.add({kind, 0, {a, b}, {}});
    }
    std::vector<ExprId> bounded() {
        return {predicate(Kind::Geq, x, constant(0)),
                predicate(Kind::Leq, x, constant(5))};
    }
};
}

TEST_CASE("Eager continuation: frozen validation survives input destruction and repeated yields") {
    unsigned allocations = 0, clauses = 0;
    Eager solver([&] { return std::make_unique<YieldingSat>(allocations, clauses); });
    {
        Query query;
        auto roots = query.bounded();
        roots.push_back(query.p);
        roots.push_back(query.predicate(Kind::Or,
            query.predicate(Kind::Eq, query.x, query.constant(3)),
            query.predicate(Kind::Eq, query.x, query.constant(4))));
        CHECK(solver.decide(query.terms, roots).status == Eager::Status::Unknown);
        REQUIRE(solver.hasPendingSearch());
    }
    const auto encodedClauses = clauses;
    // Yield once more at a caller-requested scheduling boundary. The clauses
    // and owned graph must survive both interruptions without re-encoding.
    CHECK(solver.resume(std::chrono::steady_clock::time_point::max(), [] { return true; }).status ==
          Eager::Status::Unknown);
    REQUIRE(solver.hasPendingSearch());
    const auto result = solver.resume(std::chrono::steady_clock::time_point::max());
    REQUIRE(result.status == Eager::Status::Sat);
    CHECK((result.model.at("x") == 3 || result.model.at("x") == 4));
    CHECK(result.boolModel.at("p"));
    CHECK(allocations == 1);
    CHECK(clauses == encodedClauses);
    CHECK_FALSE(solver.hasPendingSearch());
}

TEST_CASE("Eager continuation: cancel and new queries discard obsolete state") {
    unsigned allocations = 0, clauses = 0;
    Eager solver([&] { return std::make_unique<YieldingSat>(allocations, clauses); });
    Query query;
    auto roots = query.bounded();
    roots.push_back(query.predicate(Kind::Eq, query.x, query.constant(1)));
    REQUIRE(solver.decide(query.terms, roots).status == Eager::Status::Unknown);
    REQUIRE(solver.hasPendingSearch());
    roots.back() = query.predicate(Kind::Eq, query.x, query.constant(2));
    REQUIRE(solver.decide(query.terms, roots).status == Eager::Status::Unknown);
    REQUIRE(solver.hasPendingSearch());
    const auto result = solver.resume(std::chrono::steady_clock::time_point::max());
    REQUIRE(result.status == Eager::Status::Sat);
    CHECK(result.model.at("x") == 2);
    CHECK(allocations == 2);
    REQUIRE(solver.decide(query.terms, roots).status == Eager::Status::Unknown);
    solver.cancel();
    CHECK_FALSE(solver.hasPendingSearch());
    CHECK(solver.resume(std::chrono::steady_clock::time_point::max()).status == Eager::Status::Unknown);
}

TEST_CASE("Eager continuation: only a complete integer interpretation can refute") {
    for (bool real : {false, true}) {
        CAPTURE(real);
        unsigned allocations = 0, clauses = 0;
        Eager solver([&] { return std::make_unique<YieldingSat>(allocations, clauses); });
        Query query(real);
        auto roots = query.bounded();
        roots.push_back(query.p);
        roots.push_back(query.terms.add({Kind::Not, 0, {query.p}, {}}));
        REQUIRE(solver.decide(query.terms, roots).status == Eager::Status::Unknown);
        REQUIRE(solver.hasPendingSearch());
        const auto result = solver.resume(std::chrono::steady_clock::time_point::max());
        CHECK(result.status == (real ? Eager::Status::Unknown : Eager::Status::Unsat));
        CHECK_FALSE(solver.hasPendingSearch());
    }
}
