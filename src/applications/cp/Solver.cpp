#include "applications/cp/Solver.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::cp {
SolverAnswer Solver::solve(const Problem& problem) {
    SolverAnswer answer;
    if(!decide_){answer.reason="decision oracle is not attached";return answer;}
    auto query=problem.constraints;
    using K=SOMTParser::NODE_KIND;using Node=SOMTParser::Node;
    auto make=[](K kind,std::vector<Node> args){return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),kind,SOMTParser::kindToString(kind),std::move(args));};
    for(const auto& domain:problem.domains) {
        auto variable=domain.variable;
        if(!variable || variable->getKind()!=K::NT_VAR || !variable->getSort()){answer.reason="domain requires a free variable";return answer;}
        if(domain.kind==Domain::Kind::Enumeration) {
            std::vector<Node> alternatives;
            for(auto value:domain.values) {
                if(!value || !value->getSort() || !(*value->getSort()==*variable->getSort())){answer.reason="domain value sort mismatch";return answer;}
                alternatives.push_back(make(K::NT_EQ,{variable,value}));
            }
            query.push_back(alternatives.empty()?make(K::NT_CONST_FALSE,{}):make(K::NT_OR,alternatives));
        } else if(domain.kind==Domain::Kind::Interval) {
            if(!(variable->getSort()->isInt() || variable->getSort()->isReal())){answer.reason="interval domain requires arithmetic sort";return answer;}
            if(domain.lower)query.push_back(make(K::NT_LE,{domain.lower,variable}));
            if(domain.upper)query.push_back(make(K::NT_LE,{variable,domain.upper}));
        }
    }
    for(const auto& group:problem.allDifferent)if(group.size()>1)query.push_back(make(K::NT_DISTINCT,group));
    return decide_(query);
}
}
