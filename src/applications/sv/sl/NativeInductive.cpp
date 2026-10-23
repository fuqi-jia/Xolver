#include "applications/sv/sl/InductiveExpansion.h"
#include <algorithm>

namespace xolver::sl {
using namespace detail::inductive;
using detail::Stop;
namespace {
void summaries(Unfold &unfold, const std::vector<PredicateInvariant> &candidates,
               const std::vector<std::size_t> &retained) {
    unfold.summaries.clear();
    std::unordered_map<Node, std::vector<Node>> groups;
    for (auto i : retained)
        groups[candidates[i].predicate].push_back(candidates[i].property);
    for (auto &[predicate, properties] : groups)
        unfold.summaries[predicate] = operation(K::NT_AND, std::move(properties));
}
InductiveInference infer(Unfold &unfold, const std::shared_ptr<SOMTParser::Sort> &location,
                         const std::shared_ptr<SOMTParser::Sort> &data,
                         const std::vector<Node> &declarations,
                         const std::vector<PredicateInvariant> &candidates) {
    auto &work = unfold.work;
    InductiveInference answer;
    for (std::size_t i = 0; i < candidates.size(); ++i) {
        const auto &candidate = candidates[i];
        if (!unfold.definitions.count(candidate.predicate) || !candidate.property ||
            !candidate.property->getSort() || !candidate.property->getSort()->isBool())
            throw Stop("inductive invariant requires a declared predicate and Boolean property");
        const auto &definition = *unfold.definitions.at(candidate.predicate);
        unfold.collect({candidate.property});
        unfold.scope(candidate.property,
                     {definition.parameters.begin(), definition.parameters.end()});
        if (unfold.recursive(candidate.property))
            throw Stop("inductive invariant properties must not contain recursive predicates");
        answer.retained.push_back(i);
    }
    for (;;) {
        summaries(unfold, candidates, answer.retained);
        std::vector<std::size_t> retained;
        std::vector<std::vector<Node>> obligations;
        for (auto i : answer.retained) {
            work.tick();
            const auto &candidate = candidates[i];
            const auto &definition = *unfold.definitions.at(candidate.predicate);
            std::unordered_map<Node, Node> formals;
            auto symbols = declarations;
            for (auto p : definition.parameters) {
                auto fresh = unfold.fresh(p, true);
                formals[p] = fresh;
                symbols.push_back(fresh);
            }
            auto body = unfold.formula(unfold.substitute(definition.body, formals), false, 0);
            auto property = unfold.substitute(candidate.property, formals);
            std::vector<Node> query{body, operation(K::NT_NOT, {property})};
            work.tick();
            auto checked = decideNative(location, data, query, symbols,
                                        {work.limits.maxSteps - work.steps, work.limits.maxDepth});
            work.tick(checked.work);
            if (checked.result == Result::Unsat) {
                retained.push_back(i);
                obligations.push_back(std::move(query));
            } else {
                (checked.result == Result::Sat ? answer.refuted : answer.undecided).push_back(i);
            }
        }
        if (retained == answer.retained) {
            answer.obligations = std::move(obligations);
            break;
        }
        answer.retained = std::move(retained);
        // Weaker summaries can invalidate other predicates, including mutual recursion.
    }
    for (auto i : answer.retained)
        answer.invariants.push_back(candidates[i]);
    answer.complete = true;
    answer.work = work.steps;
    if (!answer.undecided.empty())
        answer.reason = "undecided inductive candidates discarded";
    return answer;
}
} // namespace

InductiveInference inferInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                                        const std::shared_ptr<SOMTParser::Sort> &data,
                                        const std::vector<Node> &declarations,
                                        const std::vector<InductiveDefinition> &definitions,
                                        const std::vector<PredicateInvariant> &candidates,
                                        Limits limits) {
    detail::Work work{limits};
    InductiveInference answer;
    try {
        heapSorts(location, data);
        Unfold unfold{work};
        prepare(unfold, {}, declarations, definitions);
        return infer(unfold, location, data, declarations, candidates);
    } catch (const std::exception &e) {
        answer.reason = e.what();
        answer.work = work.steps;
    }
    return answer;
}

InductiveAnswer solveInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                                     const std::shared_ptr<SOMTParser::Sort> &data,
                                     const std::vector<Node> &assertions,
                                     const std::vector<Node> &declarations,
                                     const std::vector<InductiveDefinition> &definitions,
                                     const std::vector<PredicateInvariant> &candidates,
                                     Limits limits) {
    InductiveAnswer result;
    detail::Work work{limits};
    try {
        heapSorts(location, data);
        Unfold unfold{work};
        prepare(unfold, assertions, declarations, definitions);
        result.inference = infer(unfold, location, data, declarations, candidates);
        struct Approximation {
            std::size_t fuel;
            uint64_t allowance = 4096;
            bool lowerDone = false, upperDone = false;
            std::vector<Node> lower, upper;
        };
        std::vector<Approximation> pending;
        std::size_t nextApproximation = 0;
        for (;;) {
            work.tick();
            pending.push_back({nextApproximation++});
            for (auto &task : pending) {
                work.tick();
                for (bool lower : {true, false}) {
                    bool &complete = lower ? task.lowerDone : task.upperDone;
                    if (complete)
                        continue;
                    auto &approximants = lower ? task.lower : task.upper;
                    if (approximants.empty())
                        for (const auto &root : assertions)
                            approximants.push_back(unfold.formula(root, lower, task.fuel));
                    work.tick();
                    auto answer = decideNative(
                        location, data, approximants, declarations,
                        {std::min(task.allowance, limits.maxSteps - work.steps), limits.maxDepth});
                    work.tick(answer.work);
                    if ((lower && answer.result == Result::Sat) ||
                        (!lower && answer.result == Result::Unsat)) {
                        answer.work = work.steps;
                        result.decision = std::move(answer);
                        result.unfoldingDepth = task.fuel;
                        return result;
                    }
                    complete = answer.result != Result::Unknown;
                }
                task.allowance =
                    task.allowance > limits.maxSteps / 2 ? limits.maxSteps : task.allowance * 2;
            }
            work.tick(pending.size());
            pending.erase(
                std::remove_if(pending.begin(), pending.end(),
                               [](const auto &task) { return task.upperDone && task.lowerDone; }),
                pending.end());
        }
    } catch (const std::exception &e) {
        result.decision = {Result::Unknown, e.what(), {}, work.steps};
    }
    return result;
}
NativeDecision decideInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                                     const std::shared_ptr<SOMTParser::Sort> &data,
                                     const std::vector<Node> &assertions,
                                     const std::vector<Node> &declarations,
                                     const std::vector<InductiveDefinition> &definitions,
                                     Limits limits) {
    return solveInductiveNative(location, data, assertions, declarations, definitions, {}, limits)
        .decision;
}
NativeDecision replayInductiveUnsat(const std::shared_ptr<SOMTParser::Sort> &location,
                                    const std::shared_ptr<SOMTParser::Sort> &data,
                                    const std::vector<Node> &assertions,
                                    const std::vector<Node> &declarations,
                                    const std::vector<InductiveDefinition> &definitions,
                                    const std::vector<PredicateInvariant> &invariants,
                                    std::size_t depth, Limits limits) {
    detail::Work work{limits};
    try {
        heapSorts(location, data);
        Unfold unfold{work};
        prepare(unfold, assertions, declarations, definitions);
        auto checked = infer(unfold, location, data, declarations, invariants);
        if (!checked.undecided.empty())
            return {Result::Unknown, "certificate invariant remains undecided", {}, work.steps};
        if (checked.retained.size() != invariants.size())
            return {Result::Sat, "certificate invariant is not inductive", {}, work.steps};
        std::vector<Node> query;
        for (auto n : assertions)
            query.push_back(unfold.formula(n, false, depth));
        work.tick();
        auto result = decideNative(location, data, query, declarations,
                                   {limits.maxSteps - work.steps, limits.maxDepth});
        work.tick(result.work);
        result.work = work.steps;
        return result;
    } catch (const std::exception &e) {
        return {Result::Unknown, e.what(), {}, work.steps};
    }
}
} // namespace xolver::sl
