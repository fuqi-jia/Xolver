#include "applications/smt/lia/Solver.h"
#include "quantifiers/integer/NativeFormula.h"
#include "evidence/PresburgerTrace.h"

namespace xolver::applications::smt::lia {
SolverAnswer solve(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& roots,
             pa::Limits limits, pa::EvidenceRequest evidence) {
    quantifiers::IntegerFormula compiler(limits, evidence);
    auto decision = compiler.decide([&] { return compiler.compile(roots); });
    SolverAnswer answer;
    answer.result = decision.result;
    answer.reason = std::move(decision.reason);
    if (decision.trace)
        answer.proof.setPresburger(pa::serializeTrace(*decision.trace, decision.result));
    if (decision.modelAvailable) {
        answer.model.emplace();
        for (const auto& [name, value] : decision.model) {
            answer.model->assignments.emplace(name, value);
            if (value != "true" && value != "false")
                answer.model->numericAssignments.emplace(name, RealValue::fromMpq(mpq_class(value)));
        }
    }
    return answer;
}
} // namespace xolver::applications::smt::lia
