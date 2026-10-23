#include "applications/sv/verification/Solver.h"
#include "ir/NativeSubstitution.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::sv::verification {
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    bool unknown = false;
    if (!decide_) {
        answer.reason = "decision oracle is not attached";
        return answer;
    }
    for (std::size_t i = 0; i < problem.obligations.size(); ++i) {
        const auto &task = problem.obligations[i];
        auto c = task.conclusion;
        if (!c || !c->getSort() || !c->getSort()->isBool()) {
            answer.status = Status::InvalidInput;
            answer.obligation = i;
            answer.reason = "conclusion must be Boolean";
            return answer;
        }
        auto query = task.assumptions;
        for (auto assumption : query)
            if (!assumption || !assumption->getSort() || !assumption->getSort()->isBool()) {
                answer.status = Status::InvalidInput;
                answer.obligation = i;
                answer.reason = "assumptions must be Boolean";
                return answer;
            }
        query.push_back(std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
                                                              SOMTParser::NODE_KIND::NT_NOT, "not",
                                                              std::vector<SOMTParser::Node>{c}));
        auto result = decide_(query);
        if (result.result == Result::Sat) {
            answer.status = Status::Invalid;
            answer.obligation = i;
            answer.counterexample = std::move(result.model);
            return answer;
        }
        if (result.result == Result::Unknown && !unknown) {
            unknown = true;
            answer.obligation = i;
            answer.reason = std::move(result.reason);
        }
    }
    answer.status = unknown ? Status::Unknown : Status::Valid;
    return answer;
}
Answer InvariantSolver::solve(const TransitionSystem &system) {
    Answer answer;
    try {
        using namespace native;
        auto roots = system.initial;
        roots.insert(roots.end(), system.transition.begin(), system.transition.end());
        roots.push_back(system.invariant);
        roots.push_back(system.safety);
        Nodes b(roots, workLimit_);
        for (auto n : roots)
            if (!n || !n->getSort() || !n->getSort()->isBool())
                throw std::invalid_argument("transition obligations must be Boolean");
        std::map<Node, Node> next, memo;
        std::set<Node> declared;
        std::set<std::string> names;
        for (const auto &[current, following] : system.state) {
            if (!current || !following || current->getKind() != K::NT_VAR ||
                following->getKind() != K::NT_VAR || !current->getSort() || !following->getSort() ||
                *current->getSort() != *following->getSort() || !declared.insert(current).second ||
                !declared.insert(following).second || !names.insert(current->getName()).second ||
                !names.insert(following->getName()).second)
                throw std::invalid_argument(
                    "state pairs require distinct, equally sorted free variables");
            next[current] = following;
        }
        std::set<Node> currentSymbols, transitionSymbols = declared;
        for (const auto &[current, following] : system.state)
            currentSymbols.insert(current);
        for (auto parameter : system.parameters) {
            if (!parameter || parameter->getKind() != K::NT_VAR || !parameter->getSort() ||
                !declared.insert(parameter).second || !names.insert(parameter->getName()).second)
                throw std::invalid_argument("parameters must be distinct free symbols");
            currentSymbols.insert(parameter);
            transitionSymbols.insert(parameter);
        }
        auto validate = [&](NativeAssertions pending, const std::set<Node> &allowed) {
            std::set<Node> seen;
            while (!pending.empty()) {
                b.budget.tick();
                auto n = pending.back();
                pending.pop_back();
                if (!n)
                    throw std::invalid_argument("null transition term");
                if (!seen.insert(n).second)
                    continue;
                if (n->getKind() == K::NT_VAR && !allowed.contains(n))
                    throw std::invalid_argument(
                        "undeclared or next-state symbol in state predicate");
                for (auto child : SOMTParser::children(n))
                    pending.push_back(child);
            }
        };
        validate(system.initial, currentSymbols);
        validate({system.invariant, system.safety}, currentSymbols);
        validate(system.transition, transitionSymbols);
        auto invariantNext = substitute(system.invariant, next, memo, b);
        auto inductiveAssumptions = system.transition;
        inductiveAssumptions.push_back(system.invariant);
        return verification::Solver(decide_).solve({{{"initiation", system.initial, system.invariant},
                                       {"consecution", inductiveAssumptions, invariantNext},
                                       {"safety", {system.invariant}, system.safety}}});
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::sv::verification
