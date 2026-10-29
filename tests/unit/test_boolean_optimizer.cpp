#include "search/optimization/BooleanOptimizer.h"
#include <doctest/doctest.h>
#include <unordered_map>

using namespace xolver;

TEST_CASE("BooleanOptimizer: signed lexicographic optima match independent enumeration") {
    for (int k = 0; k < 12; ++k) {
        auto sat = createSatSolver();
        bitblast::BitBlastEncoder encoder(*sat);
        std::vector<SatLit> variables;
        for (int i = 0; i < 3; ++i) variables.push_back(encoder.mkVar(1).bits[0]);
        sat->addClause({variables[0].negated(), variables[1].negated()});
        std::vector<optimization::BooleanObjective> objectives{
            {3, {{variables[0], k-4}, {variables[1].negated(), 2}, {variables[1], -3}}},
            {-7, {{variables[2].negated(), -7}, {variables[0], 4}}}};
        std::optional<std::vector<mpz_class>> expected;
        for (unsigned mask = 0; mask < 8; ++mask) {
            if ((mask & 3) == 3) continue;
            std::vector<mpz_class> costs(2, 0);
            costs[0] = (mask & 1 ? k-4 : 0) + (mask & 2 ? -3 : 2);
            costs[1] = (mask & 4 ? 0 : -7) + (mask & 1 ? 4 : 0);
            if (!expected || costs < *expected) expected = costs;
        }
        std::unordered_map<SatVar, bool> candidate, witness;
        WorkBudget work;
        const auto answer = optimization::minimizeBooleanLex(encoder, work, objectives,
            [&](const auto& assumptions) {
                const auto result = sat->solve(assumptions);
                if (result == SatSolver::SolveResult::Sat)
                    for (const auto variable : variables) candidate[variable.var] = sat->value(variable.var);
                return result;
            }, [&](SatLit literal) { return candidate.at(literal.var) == literal.sign; },
            [&] { auto retained = candidate; witness.swap(retained); });
        INFO(k, ": ", answer.reason);
        REQUIRE(answer.status == optimization::BooleanOptimum::Status::Optimal);
        REQUIRE(answer.hasIncumbent);
        CHECK(answer.costs == *expected);
        CHECK(answer.provedLevels == 2);
    }
}

TEST_CASE("BooleanOptimizer: initial partial cost evaluation publishes no incumbent") {
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder encoder(*sat);
    const auto a = encoder.mkVar(1).bits[0], b = encoder.mkVar(1).bits[0];
    WorkBudget work(1);
    bool published = false;
    int reads = 0;
    const auto answer = optimization::minimizeBooleanLex(encoder, work, {{0, {{a, 1}, {b, 1}}}},
        [](const auto&) { return SatSolver::SolveResult::Sat; },
        [&](SatLit) { ++reads; return true; }, [&] { published = true; });
    CHECK(answer.status == optimization::BooleanOptimum::Status::Unknown);
    CHECK_FALSE(answer.hasIncumbent);
    CHECK(answer.costs.empty());
    CHECK_FALSE(published);
    CHECK(reads == 1);
}

TEST_CASE("BooleanOptimizer: later partial evaluation preserves matching published costs and witness") {
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder encoder(*sat);
    const auto a = encoder.mkVar(1).bits[0], b = encoder.mkVar(1).bits[0];
    WorkBudget work(1000);
    int calls = 0, reads = 0;
    unsigned candidate = 0, published = 0;
    const auto answer = optimization::minimizeBooleanLex(encoder, work, {{0, {{a, 1}, {b, 1}}}},
        [&](const auto&) {
            candidate = ++calls == 1 ? 3 : 0;
            if (calls == 2) work.tick(1000-work.used()-1);
            return SatSolver::SolveResult::Sat;
        }, [&](SatLit lit) {
            ++reads;
            const bool chosen = candidate & (lit.var == a.var ? 1u : 2u);
            return chosen == lit.sign;
        }, [&] { published = candidate; });
    CHECK(calls == 2);
    CHECK(reads == 3);
    CHECK(candidate == 0);
    CHECK(published == 3);
    CHECK(answer.status == optimization::BooleanOptimum::Status::Unknown);
    REQUIRE(answer.hasIncumbent);
    REQUIRE(answer.costs.size() == 1);
    const int independentlyEvaluated = int(bool(published & 1)) + int(bool(published & 2));
    CHECK(answer.costs[0] == independentlyEvaluated);
    CHECK(answer.provedLevels == 0);
}
