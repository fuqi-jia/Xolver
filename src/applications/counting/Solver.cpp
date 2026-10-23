#include "applications/counting/Solver.h"
#include "applications/counting/Linear.h"
#include "ir/NativeFeatures.h"
#include "quantifiers/FiniteFormula.h"
#include <set>
#include <somtparser/ir/node.h>
namespace xolver::applications::counting {
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    std::set<SOMTParser::Node> seen;
    for (auto variable : problem.projection)
        if (!variable || variable->getKind() != SOMTParser::NODE_KIND::NT_VAR ||
            !seen.insert(variable).second) {
            answer.status = Status::InvalidInput;
            answer.reason = "projection requires distinct free variables";
            return answer;
        }
    auto roots = problem.assertions;
    roots.insert(roots.end(), problem.projection.begin(), problem.projection.end());
    const auto features = nativeFeatures(roots);
    if (!features.bitvector && (features.integer || features.real))
        return countLinear(problem);
    auto result =
        quantifiers::analyzeFinite(problem.assertions, problem.projection, {}, problem.limits);
    answer.reason = std::move(result.answer.reason);
    if (result.count) {
        answer.status = Status::Exact;
        answer.count = std::move(*result.count);
    }
    return answer;
}
} // namespace xolver::applications::counting
