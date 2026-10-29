#include "search/optimization/BooleanOptimizer.h"

namespace xolver::optimization {

BooleanOptimum minimizeBooleanLex(bitblast::BitBlastEncoder& encoder, WorkBudget& work,
    const std::vector<BooleanObjective>& objectives, const BooleanCheck& check,
    const BooleanValue& value, std::chrono::steady_clock::time_point deadline) {
    BooleanOptimum answer;
    std::map<std::int64_t, std::vector<bitblast::WeightedLiteral>, std::greater<>> levels;
    for (const auto& objective : objectives)
        levels[objective.priority].insert(levels[objective.priority].end(),
                                         objective.terms.begin(), objective.terms.end());
    for (const auto& [priority, terms] : levels) answer.priorities.push_back(priority);
    auto retain = [&] {
        answer.costs.clear();
        for (const auto& [priority, terms] : levels) {
            mpz_class cost = 0;
            for (const auto& term : terms) {
                work.tick();
                if (value(term.literal)) cost += term.weight;
            }
            answer.costs.push_back(std::move(cost));
        }
        answer.hasIncumbent = true;
    };
    try {
        const auto first = check({});
        if (first == SatSolver::SolveResult::Unsat) {
            answer.status = BooleanOptimum::Status::Infeasible;
            return answer;
        }
        if (first != SatSolver::SolveResult::Sat) {
            answer.reason = "initial Boolean feasibility check is incomplete";
            return answer;
        }
        retain();
        bitblast::PseudoBooleanEncoder bounds(encoder, work, deadline);
        std::size_t index = 0;
        for (const auto& [priority, terms] : levels) {
            mpz_class lower = 0, upper = answer.costs[index];
            for (const auto& term : terms)
                if (term.weight < 0) lower += term.weight;
            while (lower < upper) {
                work.tick();
                mpz_class sum = lower + upper, middle;
                mpz_fdiv_q_2exp(middle.get_mpz_t(), sum.get_mpz_t(), 1);
                const auto bound = bounds.lessEqual(terms, middle);
                if (!bound || encoder.overflowed())
                    throw ResourceExhausted("Boolean objective encoding exhausted");
                const auto result = check({*bound});
                if (result == SatSolver::SolveResult::Unsat) lower = middle + 1;
                else if (result == SatSolver::SolveResult::Sat) {
                    retain();
                    upper = answer.costs[index];
                    if (upper > middle)
                        throw std::runtime_error("Boolean objective witness violates its bound");
                } else {
                    answer.reason = "Boolean objective check is incomplete";
                    return answer;
                }
            }
            const auto optimal = bounds.lessEqual(terms, upper);
            if (!optimal || encoder.overflowed())
                throw ResourceExhausted("Boolean optimum encoding exhausted");
            encoder.assertLit(*optimal);
            ++answer.provedLevels;
            ++index;
        }
        answer.status = BooleanOptimum::Status::Optimal;
    } catch (const ResourceExhausted& error) {
        answer.reason = error.what();
    }
    return answer;
}

} // namespace xolver::optimization
