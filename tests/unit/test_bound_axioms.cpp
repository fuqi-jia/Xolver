#include "doctest/doctest.h"
#include "search/linear/BoundAxiomGenerator.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include <algorithm>
#include <array>
#include <stdexcept>
#include <vector>

using namespace xolver;

namespace {

bool compare(Relation relation, const mpq_class& value, const mpq_class& endpoint) {
    switch (relation) {
        case Relation::Lt: return value < endpoint;
        case Relation::Leq: return value <= endpoint;
        case Relation::Gt: return value > endpoint;
        case Relation::Geq: return value >= endpoint;
        case Relation::Eq: return value == endpoint;
        case Relation::Neq: return value != endpoint;
    }
    throw std::logic_error("invalid relation");
}

struct ClauseRecorder : SatSolver, DynamicAtomRegistrar {
    SatVar count = 0;
    std::vector<std::vector<SatLit>> clauses;
    SatVar newVar() override { return ++count; }
    void addClause(const std::vector<SatLit>& clause) override { clauses.push_back(clause); }
    SolveResult solve() override { throw std::logic_error("recording only"); }
    SolveResult solve(const std::vector<SatLit>&) override { return solve(); }
    bool value(SatVar) const override { throw std::logic_error("recording only"); }
    void setDeadline(std::chrono::steady_clock::time_point) override {}
    SatLit registerDynamicAtom(ExprId, TheoryId) override { return SatLit::positive(newVar()); }
};

struct Fixture {
    ClauseRecorder sat;
    TheoryAtomRegistry registry;
    Fixture() { registry.setContext(&sat, &sat); }
    SatLit atom(Relation relation, const mpq_class& endpoint, TheoryId theory,
                int coefficient = 1) {
        return registry.getOrCreateLinearBoundAtom(LinearFormKey{{{"x", coefficient}}},
                                                  relation, endpoint, theory);
    }
    bool truth(SatLit literal, const mpq_class& x) const {
        const auto* record = registry.findBySatVar(literal.var);
        if (!record) throw std::logic_error("unregistered predicate");
        const auto& payload = std::get<LinearAtomPayload>(record->payload);
        const mpq_class value = payload.lhs.terms.front().second * x;
        return compare(payload.rel, value, payload.rhs.asRational()) == literal.sign;
    }
    void checkTautologies(const std::vector<mpq_class>& points) const {
        for (const auto& clause : sat.clauses) for (const auto& x : points) {
            bool holds = false;
            for (const auto literal : clause) holds |= truth(literal, x);
            CHECK(holds);
        }
    }
};

// Endpoint values and one point in every open cell exhaust all truth vectors,
// including strict predicates at arbitrarily close rational endpoints.
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

} // namespace

TEST_CASE("Ordered bound axioms: actual clauses are tautologies for all relations and signs") {
    const std::array relations{Relation::Lt, Relation::Leq, Relation::Gt,
                               Relation::Geq, Relation::Eq, Relation::Neq};
    const std::vector<mpq_class> endpoints{mpq_class(-2, 3), 0,
        mpq_class(1, 1000003), mpq_class(1, 1000001)};
    auto allEndpoints = endpoints;
    for (const auto& value : endpoints) allEndpoints.push_back(-value);
    const auto points = cells(allEndpoints);
    for (const auto theory : {TheoryId::LIA, TheoryId::LRA})
        for (const auto a : relations) for (const auto b : relations)
            for (const auto& ca : endpoints) for (const auto& cb : endpoints)
                for (const int sign : {-1, 1}) {
                    Fixture f;
                    f.atom(a, ca, theory);
                    f.atom(b, cb, theory, sign);
                    const auto emitted = BoundAxiomGenerator::generate(f.registry, f.sat);
                    CHECK(emitted == f.sat.clauses.size());
                    f.checkTautologies(points);
                    for (const auto& record : f.registry.records()) CHECK(record.theory == theory);
                }
}

TEST_CASE("Ordered bound axioms: CNF projection matches all realizable predicate assignments") {
    for (const auto theory : {TheoryId::LIA, TheoryId::LRA}) {
        Fixture f;
        std::vector<SatLit> original;
        for (const auto relation : {Relation::Lt, Relation::Leq, Relation::Gt,
                                   Relation::Geq, Relation::Eq, Relation::Neq})
            original.push_back(f.atom(relation, 0, theory));
        original.push_back(f.atom(Relation::Leq, mpq_class(-1, 3), theory));
        original.push_back(f.atom(Relation::Gt, mpq_class(2, 5), theory, -1));
        BoundAxiomGenerator::generate(f.registry, f.sat);
        auto solver = createSatSolver();
        for (SatVar variable = 1; variable <= f.sat.count; ++variable)
            REQUIRE(solver->newVar() == variable);
        for (const auto& clause : f.sat.clauses) solver->addClause(clause);
        const auto points = cells({mpq_class(-1, 3), 0, mpq_class(-2, 5)});
        for (unsigned mask = 0; mask < (1u << original.size()); ++mask) {
            std::vector<SatLit> assumptions;
            for (size_t index = 0; index < original.size(); ++index)
                assumptions.push_back((mask & (1u << index)) ? original[index] : original[index].negated());
            const bool realizable = std::any_of(points.begin(), points.end(), [&](const auto& x) {
                return std::all_of(assumptions.begin(), assumptions.end(),
                                   [&](const auto literal) { return f.truth(literal, x); });
            });
            CHECK(solver->solve(assumptions) == (realizable ? SatSolver::SolveResult::Sat
                                                           : SatSolver::SolveResult::Unsat));
        }
    }
}

TEST_CASE("Ordered bound axioms: large inequality families use a linear chain without new atoms") {
    Fixture f;
    constexpr size_t size = 1024;
    for (size_t endpoint = 0; endpoint < size; ++endpoint)
        f.atom(Relation::Leq, mpq_class(endpoint), TheoryId::LRA);
    const auto original = f.registry.numAtomVars();
    CHECK(BoundAxiomGenerator::generate(f.registry, f.sat) == size - 1);
    CHECK(f.registry.numAtomVars() == original);
    f.checkTautologies({-1, 0, mpq_class(1, 2), 512, 1023, 1024});
}

TEST_CASE("Ordered bound axioms: equality families scale linearly with registered endpoints") {
    Fixture f;
    constexpr size_t size = 300;
    for (size_t endpoint = 0; endpoint < size; ++endpoint)
        f.atom(endpoint % 2 ? Relation::Eq : Relation::Neq, mpq_class(endpoint), TheoryId::LRA);
    CHECK(BoundAxiomGenerator::generate(f.registry, f.sat) == 5 * size - 1);
    CHECK(f.registry.numAtomVars() == 3 * size);
    f.checkTautologies({-1, 0, mpq_class(1, 2), 150, 299, 300});
    for (const auto& record : f.registry.records()) CHECK(record.theory == TheoryId::LRA);
}

TEST_CASE("Ordered bound axioms: a lone predicate needs no endpoints or clauses") {
    for (const auto relation : {Relation::Eq, Relation::Neq, Relation::Lt}) {
        Fixture f;
        f.atom(relation, mpq_class(1, 7), TheoryId::LRA);
        CHECK(BoundAxiomGenerator::generate(f.registry, f.sat) == 0);
        CHECK(f.registry.numAtomVars() == 1);
    }
}
