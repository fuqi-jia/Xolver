#include "applications/omt/Optimize.h"
#include "quantifiers/FiniteFormula.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::omt {
Answer Solver::solve(const Problem& problem) {
    Answer answer;
    if(problem.priority!=Priority::Lexicographic){answer.reason="objective priority backend unavailable";return answer;}
    std::vector<quantifiers::FiniteObjective> objectives;
    for(const auto& objective:problem.objectives) {
        auto term=objective.expression;
        if(!term || !term->getSort()){answer.status=Status::InvalidInput;answer.reason="null objective";return answer;}
        if(!term->getSort()->isBv() && !term->getSort()->isBool()){answer.reason="arithmetic optimization backend unavailable";return answer;}
        if(term->getSort()->isBv() && objective.order==Order::Arithmetic){answer.status=Status::InvalidInput;answer.reason="bit-vector objective requires explicit signedness";return answer;}
        if(term->getSort()->isBool() && objective.order==Order::SignedBitVector){answer.status=Status::InvalidInput;answer.reason="Boolean objective cannot use signed bit-vector order";return answer;}
        objectives.push_back({term,objective.direction==Direction::Maximize,objective.order==Order::SignedBitVector});
    }
    auto result=quantifiers::analyzeFinite(problem.assertions,std::nullopt,objectives,problem.limits);
    answer.reason=std::move(result.answer.reason);answer.model=std::move(result.answer.model);
    if(result.answer.result==Result::Sat) {
        answer.status=Status::Optimal;
        for(const auto& value:result.objectives)answer.objectiveValues.emplace_back(value);
    } else if(result.answer.result==Result::Unsat)answer.status=Status::Infeasible;
    return answer;
}
}
