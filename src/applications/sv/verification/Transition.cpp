#include "applications/sv/verification/Transition.h"
#include <cstdint>

namespace xolver::applications::sv::verification::detail {
using namespace native;
namespace {
NativeAssertions roots(const TransitionSystem &s, const NativeAssertions &extra) {
    auto all = extra;
    all.insert(all.end(), s.initial.begin(), s.initial.end());
    all.insert(all.end(), s.transition.begin(), s.transition.end());
    all.insert(all.end(), s.parameters.begin(), s.parameters.end());
    all.insert(all.end(), s.inputs.begin(), s.inputs.end());
    all.push_back(s.safety);
    all.push_back(s.invariant);
    for (auto [a, b] : s.state) {
        all.push_back(a);
        all.push_back(b);
    }
    return all;
}
} // namespace
Transition::Transition(const TransitionSystem &s, const NativeAssertions &extra, std::size_t limit)
    : system_(s), nodes(roots(s, extra), limit) {
    std::set<Node> declared;
    std::set<std::string> names;
    auto declare = [&](Node v) {
        if (!v || v->getKind() != K::NT_VAR || !v->getSort() || !declared.insert(v).second ||
            !names.insert(v->getName()).second)
            throw std::invalid_argument("transition symbols must be distinct typed free variables");
    };
    for (auto [current, following] : s.state) {
        declare(current);
        declare(following);
        if (*current->getSort() != *following->getSort())
            throw std::invalid_argument("state pair sort mismatch");
        stateSymbols_.insert(current);
    }
    transitionSymbols_ = declared;
    for (auto parameter : s.parameters) {
        declare(parameter);
        stateSymbols_.insert(parameter);
        transitionSymbols_.insert(parameter);
    }
    for (auto input : s.inputs) {
        declare(input);
        transitionSymbols_.insert(input);
    }
    for (auto n : s.initial)
        statePredicate(n);
    statePredicate(s.safety);
    if (s.invariant)
        statePredicate(s.invariant);
    for (auto n : extra)
        statePredicate(n);
    for (auto n : s.transition) {
        if (!n || !n->getSort() || !n->getSort()->isBool())
            throw std::invalid_argument("transition constraints must be Boolean");
        validate(n, transitionSymbols_);
    }
}
void Transition::statePredicate(Node n) {
    if (!n || !n->getSort() || !n->getSort()->isBool())
        throw std::invalid_argument("state predicates must be Boolean");
    validate(n, stateSymbols_);
}
void Transition::validate(Node n, const std::set<Node> &allowed, std::set<Node> bound) {
    Nodes::Frame frame(nodes);
    if (!n || !n->getSort())
        throw std::invalid_argument("null transition term");
    auto k = n->getKind();
    if (k == K::NT_VAR && !allowed.contains(n))
        throw std::invalid_argument("undeclared or next-state/input symbol in state predicate");
    if (k == K::NT_QUANT_VAR && !bound.contains(n))
        throw std::invalid_argument("unbound transition quantifier variable");
    if (k == K::NT_FUNC_PARAM)
        throw std::invalid_argument("unbound transition function parameter");
    if (k == K::NT_SEP_EMP || k == K::NT_SEP_PTO || k == K::NT_SEP_STAR || k == K::NT_SEP_WAND ||
        k == K::NT_SEP_NIL)
        throw std::invalid_argument(
            "transition heaps must be explicit state, not an implicit SL heap");
    if (k == K::NT_FORALL || k == K::NT_EXISTS) {
        if (n->getChildrenSize() < 2)
            throw std::invalid_argument("empty transition binder");
        for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
            auto v = n->getChild(i);
            if (!v || v->getKind() != K::NT_QUANT_VAR || !v->getSort() || !bound.insert(v).second)
                throw std::invalid_argument("invalid transition binder identity");
        }
        validate(n->getChild(0), allowed, std::move(bound));
        return;
    }
    for (auto child : SOMTParser::children(n))
        validate(child, allowed, bound);
}
Node Transition::at(Node n, std::size_t index, bool transition) {
    if (index == SIZE_MAX)
        throw ResourceExhausted("transition frame index exhausted");
    const auto last = index + (transition ? 1 : 0);
    while (states.size() <= last) {
        nodes.budget.tick();
        NativeAssertions state, input;
        for (const auto &[current, following] : system_.state)
            state.push_back(nodes.fresh(current->getSort()));
        for (auto v : system_.inputs)
            input.push_back(nodes.fresh(v->getSort()));
        states.push_back(std::move(state));
        inputs.push_back(std::move(input));
        stateMemo_.emplace_back();
        transitionMemo_.emplace_back();
    }
    std::map<Node, Node> replacements;
    for (std::size_t j = 0; j < system_.state.size(); ++j) {
        replacements[system_.state[j].first] = states[index][j];
        if (transition)
            replacements[system_.state[j].second] = states[index + 1][j];
    }
    if (transition)
        for (std::size_t j = 0; j < system_.inputs.size(); ++j)
            replacements[system_.inputs[j]] = inputs[index][j];
    return substitute(n, replacements, transition ? transitionMemo_[index] : stateMemo_[index],
                      nodes);
}
NativeAssertions Transition::at(const NativeAssertions &terms, std::size_t frame, bool transition) {
    NativeAssertions result;
    for (auto n : terms)
        result.push_back(at(n, frame, transition));
    return result;
}
Node Transition::next(Node n) {
    std::map<Node, Node> substitutions, memo;
    for (auto [a, b] : system_.state)
        substitutions[a] = b;
    return substitute(n, substitutions, memo, nodes);
}
Node Transition::image(Node predicate) {
    std::map<Node, Node> replacements, memo;
    NativeAssertions binders;
    auto bind = [&](Node n) {
        auto name = nodes.fresh(n->getSort())->getName();
        auto v = nodes.make(n->getSort(), K::NT_QUANT_VAR, {}, name);
        binders.push_back(v);
        return v;
    };
    for (auto [current, following] : system_.state) {
        replacements[current] = bind(current);
        replacements[following] = current;
    }
    for (auto input : system_.inputs)
        replacements[input] = bind(input);
    NativeAssertions body{substitute(predicate, replacements, memo, nodes)};
    for (auto n : system_.transition)
        body.push_back(substitute(n, replacements, memo, nodes));
    auto result = nodes.all(std::move(body));
    if (binders.empty())
        return result;
    binders.insert(binders.begin(), result);
    return nodes.logical(K::NT_EXISTS, std::move(binders));
}
Node Transition::simplePath(std::size_t depth) {
    at(nodes.boolean(true), depth);
    NativeAssertions distinct;
    for (std::size_t i = 0; i < depth; ++i)
        for (std::size_t j = i + 1; j <= depth; ++j) {
            NativeAssertions equalities;
            for (std::size_t k = 0; k < system_.state.size(); ++k)
                equalities.push_back(nodes.equal(states[i][k], states[j][k]));
            distinct.push_back(nodes.negate(nodes.all(equalities)));
        }
    return nodes.all(distinct);
}
} // namespace xolver::applications::sv::verification::detail
