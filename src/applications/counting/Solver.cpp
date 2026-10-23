#include "applications/counting/Solver.h"
#include "quantifiers/FiniteFormula.h"
#include <somtparser/ir/node.h>
#include <set>
namespace xolver::applications::counting {
Answer Solver::solve(const Problem& problem) {
    Answer answer;std::set<SOMTParser::Node> seen;
    for(auto variable:problem.projection)
        if(!variable || variable->getKind()!=SOMTParser::NODE_KIND::NT_VAR || !seen.insert(variable).second) {
            answer.status=Status::InvalidInput;answer.reason="projection requires distinct free variables";return answer;
        }
    auto result=quantifiers::analyzeFinite(problem.assertions,problem.projection,{},problem.limits);
    answer.reason=std::move(result.answer.reason);
    if(result.count){answer.status=Status::Exact;answer.count=std::move(*result.count);}
    return answer;
}
}
