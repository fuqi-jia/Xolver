#include "applications/verification/model_checking/Reachability.h"
#include "applications/verification/model_checking/Transition.h"

namespace xolver::applications::verification::model_checking {
SafetyAnswer ReachabilitySolver::solve(const TransitionSystem &system) {
    SafetyAnswer answer;
    try {
        if (!decide_)
            throw std::invalid_argument("decision oracle is not attached");
        detail::Transition t(system, {}, limits_.work);
        auto ask = [&](const NativeAssertions &q) {
            t.nodes.budget.tick();
            if (limits_.queries && answer.queries >= limits_.queries)
                throw ResourceExhausted("verification query budget exhausted");
            ++answer.queries;
            return decide_(q);
        };
        auto frontier = t.nodes.all(system.initial);
        NativeAssertions regions{frontier};
        auto path = t.at(system.initial, 0);
        std::string closureReason;
        for (std::size_t depth = 0;; ++depth) {
            if (depth) {
                auto edge = t.at(system.transition, depth - 1, true);
                path.insert(path.end(), edge.begin(), edge.end());
            }
            auto query = path;
            query.push_back(t.nodes.negate(t.at(system.safety, depth)));
            auto checked = ask(query);
            if (checked.result == Result::Sat) {
                answer.status = SafetyStatus::Unsafe;
                Counterexample trace;
                trace.states.assign(t.states.begin(), t.states.begin() + depth + 1);
                trace.inputs.assign(t.inputs.begin(), t.inputs.begin() + depth);
                trace.query = std::move(query);
                trace.model = std::move(checked.model);
                answer.counterexample = std::move(trace);
                return answer;
            }
            if (checked.result == Result::Unknown) {
                answer.reason = "reachable counterexample query: " + checked.reason;
                return answer;
            }
            answer.checkedDepth = depth;
            // R is exactly the states reachable in at most depth edges. The
            // checked bases establish R => P. Closure makes R inductive.
            auto reached = t.nodes.any(regions);
            query = system.transition;
            query.push_back(reached);
            query.push_back(t.nodes.negate(t.next(reached)));
            auto closed = ask(query);
            if (closed.result == Result::Unsat) {
                answer.status = SafetyStatus::Safe;
                answer.certificate = SafetyCertificate{SafetyProof::Invariant, depth, {reached}};
                return answer;
            }
            if (closed.result == Result::Unknown)
                closureReason = closed.reason;
            if (depth == limits_.depth)
                break;
            frontier = t.image(frontier);
            regions.push_back(frontier);
        }
        answer.reason = "symbolic reachability depth budget exhausted";
        if (!closureReason.empty())
            answer.reason += "; transition closure: " + closureReason;
    } catch (const std::invalid_argument &e) {
        answer.status = SafetyStatus::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::verification::model_checking
