#include "decision/sl/HeapSearch.h"
#include <algorithm>
#include <compare>
#include <set>

namespace xolver::sl {
namespace {
using namespace detail;
struct State {
    std::vector<std::size_t> cells; // 0=unallocated, otherwise record index+1
    std::size_t anonymous = 0;
    auto operator<=>(const State&) const = default;
};
bool nextChoices(std::vector<std::size_t>& digits, std::size_t max) {
    std::size_t i = 0;
    while (i < digits.size() && digits[i] == max) digits[i++] = 0;
    if (i == digits.size()) return false;
    ++digits[i];
    return true;
}

// Finite abstraction: exact cells at named locations, and a saturated count of
// anonymous cells. All data not equal to a mentioned record has one color.
class Decision {
    const Prepared& p;
    const std::map<Location, uint64_t>& stack;
    const Vocabulary& v;
    Work& work;
    std::map<std::pair<FormulaId, State>, bool> memo;

    bool compute(FormulaId id, const State& state) {
        const auto& n = p.formula.nodes[id];
        using K = FormulaNode::Kind;
        switch (n.kind) {
        case K::Boolean: return n.boolean;
        case K::Relation:
            return (stack.at(n.relation.left) == stack.at(n.relation.right)) == n.relation.equal;
        case K::Emp:
            return !state.anonymous &&
                std::none_of(state.cells.begin(), state.cells.end(), [](auto x) { return x != 0; });
        case K::PointsTo: {
            if (state.anonymous) return false;
            const auto address = stack.at(n.cell.address);
            if (!address) return false;
            auto it = std::lower_bound(v.addresses.begin(), v.addresses.end(), address);
            const auto i = std::size_t(it - v.addresses.begin());
            if (i == state.cells.size() || !state.cells[i]) return false;
            if (std::count_if(state.cells.begin(), state.cells.end(),
                              [](auto x) { return x != 0; }) != 1) return false;
            return v.records[state.cells[i] - 1] == instantiate(n.cell, stack);
        }
        case K::Not: return !holds(n.children[0], state);
        case K::And: return holds(n.children[0], state) && holds(n.children[1], state);
        case K::Or: return holds(n.children[0], state) || holds(n.children[1], state);
        case K::Star: {
            std::vector<std::size_t> allocated;
            for (std::size_t i = 0; i < state.cells.size(); ++i)
                if (state.cells[i]) allocated.push_back(i);
            std::vector<std::size_t> partition(allocated.size(), 0);
            do {
                work.tick();
                State a{std::vector<std::size_t>(state.cells.size())}, b = a;
                for (std::size_t i = 0; i < allocated.size(); ++i)
                    (partition[i] ? b : a).cells[allocated[i]] = state.cells[allocated[i]];
                for (std::size_t count = 0;; ++count) {
                    a.anonymous = count; b.anonymous = state.anonymous - count;
                    if (holds(n.children[0], a) && holds(n.children[1], b)) return true;
                    if (count == state.anonymous) break;
                }
            } while (nextChoices(partition, 1));
            return false;
        }
        case K::Wand: {
            std::vector<std::size_t> available;
            for (std::size_t i = 0; i < state.cells.size(); ++i)
                if (!state.cells[i]) available.push_back(i);
            std::vector<std::size_t> choice(available.size(), 0);
            const auto bound = std::max(p.width[n.children[0]], p.width[n.children[1]]);
            do {
                work.tick();
                State extension{std::vector<std::size_t>(state.cells.size())}, combined = state;
                for (std::size_t i = 0; i < available.size(); ++i)
                    extension.cells[available[i]] = combined.cells[available[i]] = choice[i];
                for (std::size_t count = 0;; ++count) {
                    extension.anonymous = count;
                    const auto cap = p.width[n.children[1]];
                    // Only the consequent observes the union; saturated addition
                    // avoids overflowing for a heavily shared formula DAG.
                    combined.anonymous = std::min(cap, state.anonymous);
                    combined.anonymous += std::min(count, cap - combined.anonymous);
                    if (holds(n.children[0], extension) && !holds(n.children[1], combined))
                        return false;
                    if (count == bound) break;
                }
            } while (nextChoices(choice, v.records.size()));
            return true;
        }
        }
        throw Stop("invalid spatial connective");
    }
public:
    Decision(const Prepared& p, const std::map<Location, uint64_t>& s,
             const Vocabulary& v, Work& w) : p(p), stack(s), v(v), work(w) {}
    bool holds(FormulaId id, const State& input) {
        work.tick();
        // Charge for state width as well as calls. Otherwise a large location
        // vocabulary can exhaust memory long before the call budget expires.
        work.tick(input.cells.size());
        work.tick(input.cells.size());
        work.tick(input.cells.size());
        State state = input;
        state.anonymous = std::min(state.anonymous, p.width[id]);
        const auto key = std::pair{id, state};
        if (auto it = memo.find(key); it != memo.end()) return it->second;
        const bool result = compute(id, state);
        memo.emplace(key, result);
        return result;
    }
};
}

Outcome detail::solveHeap(const Prepared& p, const std::map<Location, uint64_t>& stack,
                          Work& work) {
    for (auto symbol : p.symbols) {
        work.tick();
        const auto it = stack.find(symbol);
        if (it == stack.end()) throw Stop("missing location interpretation");
        if (symbol == 0 && it->second != 0) throw Stop("nil interpretation is not zero");
    }
    // Reject stacks whose pure Boolean consequences are already false. Spatial
    // nodes stay indeterminate; in particular a wand never becomes a pure atom.
    std::vector<int8_t> pure(p.formula.nodes.size(), -1);
    for (size_t i = 0; i < pure.size(); ++i) {
        if (!p.reachable[i]) continue;
        work.tick();
        const auto& n = p.formula.nodes[i];
        using K = FormulaNode::Kind;
        if (n.kind == K::Boolean) pure[i] = n.boolean;
        else if (n.kind == K::Relation)
            pure[i] = (stack.at(n.relation.left) == stack.at(n.relation.right)) == n.relation.equal;
        else if (n.kind == K::Not && pure[n.children[0]] >= 0)
            pure[i] = !pure[n.children[0]];
        else if (n.kind == K::And || n.kind == K::Or) {
            const auto a = pure[n.children[0]], b = pure[n.children[1]];
            if (n.kind == K::And) {
                if (a == 0 || b == 0) pure[i] = 0;
                else if (a == 1 && b == 1) pure[i] = 1;
            } else {
                if (a == 1 || b == 1) pure[i] = 1;
                else if (a == 0 && b == 0) pure[i] = 0;
            }
        }
    }
    if (pure[p.formula.root] == 0) return {Result::Unsat, {}, {}, {}};
    auto v = vocabulary(p, stack, work);
    // Only points-to addresses distinguish individual allocation sites. Values
    // used solely as data or pure terms are observationally anonymous. Keep the
    // full stack vocabulary for fresh witness addresses and for the independent
    // checker, which continues to enumerate the larger representative set.
    auto reserved = v.addresses;
    std::set<uint64_t> observed;
    for (std::size_t i = 0; i < p.formula.nodes.size(); ++i) {
        if (!p.reachable[i]) continue;
        work.tick();
        const auto& n = p.formula.nodes[i];
        if (n.kind == FormulaNode::Kind::PointsTo) {
            const auto address = stack.at(n.cell.address);
            if (address) observed.insert(address);
        }
    }
    v.addresses.assign(observed.begin(), observed.end());
    Decision decision(p, stack, v, work);
    State state{std::vector<std::size_t>(v.addresses.size())};
    do {
        for (std::size_t count = 0;; ++count) {
            state.anonymous = count;
            if (decision.holds(p.formula.root, state)) {
                Model model{stack, {}};
                for (std::size_t i = 0; i < state.cells.size(); ++i)
                    if (state.cells[i])
                        model.heap.emplace(v.addresses[i], v.records[state.cells[i] - 1]);
                const Vocabulary fresh{reserved, {}};
                for (auto address : freshAddresses(fresh, model.heap, count, work))
                    model.heap.emplace(address, v.records.front());
                Limits remaining{work.limits.maxSteps - work.steps, work.limits.maxDepth};
                auto checked = evaluate(p.formula, model, remaining);
                // The same budget is used by subsequent stack candidates and
                // theory calls; witness checking must not get a free allowance.
                work.tick(checked.steps);
                if (!checked.holds.has_value())
                    return {Result::Unknown, {}, {}, checked.reason};
                if (!*checked.holds)
                    return {Result::Unknown, {}, {}, "independent SL model checker rejected witness"};
                return {Result::Sat, std::move(model), {}, {}};
            }
            if (count == p.width[p.formula.root]) break;
        }
    } while (nextChoices(state.cells, v.records.size()));
    return {Result::Unsat, {}, {}, {}};
}

Outcome detail::solveArrangements(const Prepared& p, Work& work) {
        // Restricted-growth strings enumerate each stack equality partition once.
        // The first symbol is nil; its class is fixed at 0.
        std::vector<uint64_t> assignment(p.symbols.size(), 0);
        while (true) {
            work.tick();
            std::map<Location, uint64_t> stack;
            for (std::size_t i = 0; i < assignment.size(); ++i)
                stack.emplace(p.symbols[i], assignment[i]);
            auto result = detail::solveHeap(p, stack, work);
            if (result.result != Result::Unsat) return result;
            bool advanced = false;
            for (std::size_t i = assignment.size() - 1; i > 0; --i) {
                const auto max = *std::max_element(assignment.begin(), assignment.begin() + i);
                if (assignment[i] <= max) {
                    ++assignment[i];
                    std::fill(assignment.begin() + i + 1, assignment.end(), 0);
                    advanced = true;
                    break;
                }
            }
            if (!advanced) break;
        }
        return {Result::Unsat, {}, {}, {}};
}

Outcome solve(const Formula& input, Limits limits) {
    Work work{limits};
    try {
        auto p = prepare(input, work);
        return detail::solveArrangements(p, work);
    } catch (const Stop& e) {
        return {Result::Unknown, {}, {}, e.what()};
    }
}
} // namespace xolver::sl
