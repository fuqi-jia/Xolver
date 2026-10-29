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
        std::unordered_map<SatVar, bool> witness;
        WorkBudget work;
        const auto answer = optimization::minimizeBooleanLex(encoder, work, objectives,
            [&](const auto& assumptions) {
                const auto result = sat->solve(assumptions);
                if (result == SatSolver::SolveResult::Sat)
                    for (const auto variable : variables) witness[variable.var] = sat->value(variable.var);
                return result;
            }, [&](SatLit literal) { return witness.at(literal.var) == literal.sign; });
        INFO(k, ": ", answer.reason);
        REQUIRE(answer.status == optimization::BooleanOptimum::Status::Optimal);
        REQUIRE(answer.hasIncumbent);
        CHECK(answer.costs == *expected);
        CHECK(answer.provedLevels == 2);
    }
}

TEST_CASE("BooleanOptimizer: exhausted encoding retains a checked incumbent without optimality") {
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder encoder(*sat);
    const auto variable = encoder.mkVar(1).bits[0];
    bool witness = false;
    WorkBudget work(1);
    const auto answer = optimization::minimizeBooleanLex(encoder, work, {{0, {{variable, 1}}}},
        [&](const auto& assumptions) {
            const auto result = sat->solve(assumptions);
            if (result == SatSolver::SolveResult::Sat) witness = sat->value(variable.var);
            return result;
        }, [&](SatLit literal) { return witness == literal.sign; });
    CHECK(answer.status == optimization::BooleanOptimum::Status::Unknown);
    REQUIRE(answer.hasIncumbent);
    REQUIRE(answer.costs.size() == 1);
    CHECK(answer.costs[0] == (witness ? 1 : 0));
    CHECK(answer.provedLevels == 0);
}
