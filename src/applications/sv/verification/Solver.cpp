#include "applications/sv/verification/Solver.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::sv::verification {
Answer Solver::solve(const Problem& problem) {
    Answer answer;bool unknown=false;
    if(!decide_){answer.reason="decision oracle is not attached";return answer;}
    for(std::size_t i=0;i<problem.obligations.size();++i) {
        const auto& task=problem.obligations[i];auto c=task.conclusion;
        if(!c || !c->getSort() || !c->getSort()->isBool()){answer.status=Status::InvalidInput;answer.obligation=i;answer.reason="conclusion must be Boolean";return answer;}
        auto query=task.assumptions;
        query.push_back(std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),SOMTParser::NODE_KIND::NT_NOT,"not",std::vector<SOMTParser::Node>{c}));
        auto result=decide_(query);
        if(result.result==Result::Sat){answer.status=Status::Invalid;answer.obligation=i;answer.counterexample=std::move(result.model);return answer;}
        if(result.result==Result::Unknown && !unknown){unknown=true;answer.obligation=i;answer.reason=std::move(result.reason);}
    }
    answer.status=unknown?Status::Unknown:Status::Valid;return answer;
}
}
