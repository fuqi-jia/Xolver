#include "contracts/SeparationFormula.h"
#include <algorithm>
#include <functional>

namespace xolver::sl {
namespace {
using namespace detail;

// Concrete-heap semantics. This deliberately does not use the decision
// procedure's symbolic cell states, memo table or anonymous-cell arithmetic.
class Checker {
    const Prepared& p;
    const std::map<Location, uint64_t>& stack;
    const Vocabulary& v;
    Work& work;
public:
    Checker(const Prepared& p, const std::map<Location, uint64_t>& s,
            const Vocabulary& v, Work& w) : p(p), stack(s), v(v), work(w) {}

    bool holds(FormulaId id, const Heap& heap) {
        work.tick();
        const auto& n = p.formula.nodes[id];
        using K = FormulaNode::Kind;
        switch (n.kind) {
        case K::Boolean: return n.boolean;
        case K::Relation:
            return (stack.at(n.relation.left) == stack.at(n.relation.right)) == n.relation.equal;
        case K::Emp: return heap.empty();
        case K::PointsTo: {
            const auto address = stack.at(n.cell.address);
            auto it = heap.find(address);
            return address != 0 && heap.size() == 1 && it != heap.end() &&
                it->second == instantiate(n.cell, stack);
        }
        case K::Not: return !holds(n.children[0], heap);
        case K::And: return holds(n.children[0], heap) && holds(n.children[1], heap);
        case K::Or: return holds(n.children[0], heap) || holds(n.children[1], heap);
        case K::Star: {
            // Enumerate actual partitions, including the empty parts. No labels
            // or guessed partition is reused under a negative occurrence.
            std::vector<uint64_t> addresses;
            for (const auto& [address, ignored] : heap) addresses.push_back(address);
            std::vector<bool> right(addresses.size(), false);
            while (true) {
                work.tick();
                work.tick(heap.size());
                Heap a, b;
                for (std::size_t i = 0; i < addresses.size(); ++i)
                    (right[i] ? b : a).emplace(addresses[i], heap.at(addresses[i]));
                if (holds(n.children[0], a) && holds(n.children[1], b)) return true;
                std::size_t i = 0;
                while (i < right.size() && right[i]) right[i++] = false;
                if (i == right.size()) return false;
                right[i] = true;
            }
        }
        case K::Wand: {
            // Fixing the stack, an unmentioned address can only be observed via
            // heap size. Truth stabilizes at width(formula). Every extension
            // therefore has a representative with at most max(width(A),width(B))
            // fresh cells, plus the (finitely many) mentioned addresses. Their
            // data is unobservable; at mentioned addresses retain every record
            // equality class, including a record unlike every mentioned record.
            const auto bound = std::max(p.width[n.children[0]], p.width[n.children[1]]);
            auto fresh = freshAddresses(v, heap, bound, work);
            std::vector<uint64_t> available;
            for (auto address : v.addresses)
                if (!heap.count(address)) available.push_back(address);
            std::vector<std::size_t> choices(available.size(), 0);
            while (true) {
                work.tick();
                work.tick(available.size());
                Heap extension;
                for (std::size_t i = 0; i < choices.size(); ++i)
                    if (choices[i]) extension.emplace(available[i], v.records[choices[i] - 1]);
                for (std::size_t count = 0;; ++count) {
                    work.tick();
                    if (holds(n.children[0], extension)) {
                        work.tick(heap.size());
                        work.tick(extension.size());
                        Heap combined = heap;
                        combined.insert(extension.begin(), extension.end());
                        if (!holds(n.children[1], combined)) return false;
                    }
                    if (count == bound) break;
                    extension.emplace(fresh[count], v.records.front());
                }
                std::size_t i = 0;
                while (i < choices.size() && choices[i] == v.records.size())
                    choices[i++] = 0;
                if (i == choices.size()) return true;
                ++choices[i];
            }
        }
        }
        throw Stop("invalid spatial connective");
    }
};
}

Evaluation evaluate(const Formula& input, const Model& model, Limits limits) {
    detail::Work work{limits};
    try {
        auto p = detail::prepare(input, work);
        auto v = detail::vocabulary(p, model.locations, work);
        auto heap = detail::canonicalHeap(p, model, work);
        const bool holds = Checker(p, model.locations, v, work).holds(input.root, heap);
        return {holds, work.steps, {}};
    } catch (const detail::Stop& e) {
        return {{}, work.steps, e.what()};
    }
}
} // namespace xolver::sl
