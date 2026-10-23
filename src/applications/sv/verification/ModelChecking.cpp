#include "applications/sv/verification/ModelChecking.h"
#include "applications/sv/verification/Transition.h"
#include <numeric>

namespace xolver::applications::sv::verification {
namespace {
using namespace native;
struct Session {
    const DecisionOracle &decide;
    CheckLimits limits;
    detail::Transition transition;
    std::size_t queries = 0;
    std::size_t *reportedQueries = nullptr;
    Session(const DecisionOracle &oracle, const TransitionSystem &s, const NativeAssertions &extra,
            CheckLimits l)
        : decide(oracle), limits(l), transition(s, extra, l.work) {
        if (!decide)
            throw std::invalid_argument("decision oracle is not attached");
    }
    SolverAnswer ask(const NativeAssertions &q) {
        transition.nodes.budget.tick();
        if (limits.queries && queries >= limits.queries)
            throw ResourceExhausted("verification query budget exhausted");
        ++queries;
        if (reportedQueries)
            *reportedQueries = queries;
        return decide(q);
    }
    SolverAnswer obligation(const NativeAssertions &assumptions, Node conclusion) {
        auto query = assumptions;
        query.push_back(transition.nodes.negate(conclusion));
        return ask(query);
    }
};
void append(NativeAssertions &to, const NativeAssertions &from) {
    to.insert(to.end(), from.begin(), from.end());
}
InferenceAnswer infer(Session &s, const TransitionSystem &system,
                      const NativeAssertions &candidates) {
    InferenceAnswer result;
    auto &t = s.transition;
    auto retain = [&](std::size_t i, const SolverAnswer &answer) {
        if (answer.result == Result::Unsat)
            return true;
        (answer.result == Result::Sat ? result.refuted : result.undecided).push_back(i);
        return false;
    };
    for (std::size_t i = 0; i < candidates.size(); ++i)
        if (retain(i, s.obligation(system.initial, candidates[i])))
            result.retained.push_back(i);
    for (;;) {
        NativeAssertions assumptions = system.transition;
        for (auto i : result.retained)
            assumptions.push_back(candidates[i]);
        std::vector<std::size_t> remaining;
        for (auto i : result.retained)
            if (retain(i, s.obligation(assumptions, t.next(candidates[i]))))
                remaining.push_back(i);
        if (remaining == result.retained)
            break;
        result.retained = std::move(remaining);
        // Removing a conjunct weakens the induction hypothesis: recheck survivors.
    }
    for (auto i : result.retained)
        result.invariant.push_back(candidates[i]);
    auto assumptions = system.transition;
    append(assumptions, result.invariant);
    for (auto i : result.retained) {
        result.obligations.push_back(
            {"initiation-" + std::to_string(i), system.initial, candidates[i]});
        result.obligations.push_back(
            {"consecution-" + std::to_string(i), assumptions, t.next(candidates[i])});
    }
    result.status = InferenceStatus::Inductive;
    if (!result.undecided.empty())
        result.reason = "undecided candidates discarded; retained conjunction is inductive";
    return result;
}
NativeAssertions induction(Session &session, const TransitionSystem &system,
                           const NativeAssertions &invariant, std::size_t depth) {
    auto &t = session.transition;
    NativeAssertions query;
    for (std::size_t i = 0; i < depth; ++i) {
        append(query, t.at(invariant, i));
        query.push_back(t.at(system.safety, i));
        append(query, t.at(system.transition, i, true));
    }
    query.push_back(t.nodes.negate(t.at(system.safety, depth)));
    return query;
}
} // namespace
InferenceAnswer InferenceSolver::solve(const InferenceProblem &p) {
    InferenceAnswer answer;
    try {
        Session session(decide_, p.system, p.candidates, limits_);
        return infer(session, p.system, p.candidates);
    } catch (const std::invalid_argument &e) {
        answer.status = InferenceStatus::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
SafetyAnswer SafetySolver::solve(const SafetyProblem &p) {
    SafetyAnswer answer;
    try {
        auto candidates = p.candidates;
        if (p.system.invariant)
            candidates.push_back(p.system.invariant);
        Session session(decide_, p.system, candidates, limits_);
        session.reportedQueries = &answer.queries;
        auto &t = session.transition;
        const auto inferred = infer(session, p.system, candidates);
        const auto &invariant = inferred.invariant;
        auto safe = [&](SafetyProof proof, std::size_t depth) {
            answer.status = SafetyStatus::Safe;
            answer.certificate = SafetyCertificate{proof, depth, invariant};
        };
        NativeAssertions path = t.at(p.system.initial, 0);
        for (std::size_t depth = 0;; ++depth) {
            if (depth)
                append(path, t.at(p.system.transition, depth - 1, true));
            auto query = path;
            query.push_back(t.nodes.negate(t.at(p.system.safety, depth)));
            auto counterexample = session.ask(query);
            if (counterexample.result == Result::Sat) {
                answer.status = SafetyStatus::Unsafe;
                Counterexample trace;
                trace.states.assign(t.states.begin(), t.states.begin() + depth + 1);
                trace.inputs.assign(t.inputs.begin(), t.inputs.begin() + depth);
                trace.query = std::move(query);
                trace.model = std::move(counterexample.model);
                answer.counterexample = std::move(trace);
                return answer;
            }
            if (counterexample.result == Result::Unknown) {
                answer.reason = "reachable counterexample query: " + counterexample.reason;
                return answer;
            }
            answer.checkedDepth = depth;
            if (!depth && method_ == SafetyMethod::Induction) {
                auto implies = session.obligation(invariant, p.system.safety);
                if (implies.result == Result::Unsat) {
                    safe(SafetyProof::Invariant, 0);
                    return answer;
                }
            }
            // Every reachable state has a simple path. Excluding all simple
            // paths of this length proves the bounded base covers reachability.
            auto diameter = path;
            diameter.push_back(t.simplePath(depth));
            auto completion = session.ask(diameter);
            if (completion.result == Result::Unsat) {
                safe(SafetyProof::ReachabilityDiameter, depth);
                return answer;
            }
            if (depth && method_ == SafetyMethod::Induction) {
                auto step = session.ask(induction(session, p.system, invariant, depth));
                if (step.result == Result::Unsat) {
                    safe(SafetyProof::KInduction, depth);
                    return answer;
                }
            }
            if (depth == limits_.depth)
                break;
        }
        answer.reason = "verification depth budget exhausted; bounded absence of a counterexample "
                        "is not a safety proof";
    } catch (const std::invalid_argument &e) {
        answer.status = SafetyStatus::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
Answer CertificateSolver::solve(const CertificateProblem &p) {
    Answer answer;
    try {
        const auto &certificate = p.certificate;
        if (certificate.depth > limits_.depth)
            throw ResourceExhausted("certificate depth budget exhausted");
        Session session(decide_, p.system, certificate.invariant, limits_);
        auto &t = session.transition;
        auto check = [&](const NativeAssertions &query) {
            auto result = session.ask(query);
            if (result.result == Result::Unsat) {
                ++answer.obligation;
                return true;
            }
            answer.status = result.result == Result::Sat ? Status::Invalid : Status::Unknown;
            answer.counterexample = std::move(result.model);
            answer.reason = std::move(result.reason);
            return false;
        };
        auto obligation = [&](NativeAssertions assumptions, Node conclusion) {
            assumptions.push_back(t.nodes.negate(conclusion));
            return check(assumptions);
        };
        auto invariant = t.nodes.all(certificate.invariant);
        if (!obligation(p.system.initial, invariant))
            return answer;
        auto step = p.system.transition;
        step.push_back(invariant);
        if (!obligation(step, t.next(invariant)))
            return answer;
        if (certificate.kind == SafetyProof::Invariant) {
            if (!obligation(certificate.invariant, p.system.safety))
                return answer;
        } else {
            if (certificate.kind != SafetyProof::KInduction &&
                certificate.kind != SafetyProof::ReachabilityDiameter)
                throw std::invalid_argument("unknown safety certificate method");
            auto path = t.at(p.system.initial, 0);
            for (std::size_t i = 0;; ++i) {
                if (i)
                    append(path, t.at(p.system.transition, i - 1, true));
                if (!obligation(path, t.at(p.system.safety, i)))
                    return answer;
                if (i == certificate.depth)
                    break;
            }
            if (certificate.kind == SafetyProof::KInduction) {
                if (!certificate.depth)
                    throw std::invalid_argument("k-induction requires positive depth");
                if (!check(induction(session, p.system, certificate.invariant, certificate.depth)))
                    return answer;
            } else {
                path.push_back(t.simplePath(certificate.depth));
                if (!check(path))
                    return answer;
            }
        }
        answer.status = Status::Valid;
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::sv::verification
