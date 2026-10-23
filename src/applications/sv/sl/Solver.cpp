#include "applications/sv/sl/Solver.h"

namespace xolver::sl {
SolverAnswer solve(const Request& request, Limits limits) {
    Solver solver(limits);
    return solver.solve(request);
}
SolverAnswer Solver::solve(const Request& request) {
    NativeDecision decision;
    if (!request.location || !request.data) {
        decision.reason = "SL requires an explicit heap signature";
    } else if (request.definitions.empty()) {
        decision = decideNative(request.location, request.data, request.assertions,
                                request.declarations, limits);
    } else if (request.recursion == RecursiveSemantics::LeastFixedPoint) {
        decision = solveInductiveNative(request.location, request.data, request.assertions,
                                         request.declarations, request.definitions,
                                         request.invariantCandidates, limits).decision;
    } else {
        decision.reason = "ordinary recursive equations are outside the SL inductive semantics; "
                          "an explicit SHID logic is required for least-fixed-point predicates";
    }
    SolverAnswer answer;
    answer.result = decision.result;
    answer.reason = std::move(decision.reason);
    if (decision.model) {
        answer.model.emplace();
        answer.model->separation = decision.model;
        for (const auto& [name, value] : decision.model->assignments) {
            answer.model->assignments.emplace(name, value);
            if (!decision.model->booleans.count(name))
                answer.model->numericAssignments.emplace(name, RealValue::fromMpq(mpq_class(value)));
        }
    }
    return answer;
}
} // namespace xolver::sl
