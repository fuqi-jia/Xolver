#include "ir/PartialBooleanEvaluation.h"
#include <utility>
#include <vector>

namespace xolver {

PartialBooleanEvaluation::PartialBooleanEvaluation(const NativeTerms& terms, AtomValue atoms)
    : terms_(terms), atoms_(std::move(atoms)) {}

PartialBooleanEvaluation::Truth PartialBooleanEvaluation::evaluate(ExprId root) {
    auto value = [&](ExprId id) -> Truth {
        const auto found = values_.find(id);
        return found == values_.end() ? std::nullopt : found->second;
    };
    struct Frame { ExprId id; bool processed; };
    std::vector<Frame> pending{{root, false}};
    while (!pending.empty()) {
        auto& frame = pending.back();
        const auto id = frame.id;
        if (values_.contains(id)) { pending.pop_back(); continue; }
        if (id >= terms_.size()) {
            values_.emplace(id, std::nullopt);
            pending.pop_back();
            continue;
        }
        const auto& term = terms_.get(id);
        if (!frame.processed) {
            if (const auto kind = terms_.sortKind(term.sort); kind && *kind != SortKind::Bool) {
                values_.emplace(id, std::nullopt);
                pending.pop_back();
                continue;
            }
            if (auto known = atoms_ ? atoms_(id) : std::nullopt) {
                values_.emplace(id, known);
                pending.pop_back();
                continue;
            }
            frame.processed = true;
            switch (term.kind) {
                case Kind::Not: case Kind::And: case Kind::Or: case Kind::Implies:
                case Kind::Xor: case Kind::Ite: case Kind::Eq: case Kind::Distinct:
                    for (auto child : term.children)
                        if (!values_.contains(child)) pending.push_back({child, false});
                    continue;
                default:
                    break;
            }
        }
        pending.pop_back();
        const auto& children = term.children;
        Truth result;
        switch (term.kind) {
            case Kind::ConstBool:
                if (const auto boolean = std::get_if<bool>(&term.payload.value)) result = *boolean;
                break;
            case Kind::Not:
                if (children.size() == 1)
                    if (auto child = value(children.front())) result = !*child;
                break;
            case Kind::And: case Kind::Or: {
                const bool identity = term.kind == Kind::And;
                result = identity;
                for (auto child : children) {
                    const auto known = value(child);
                    if (known && *known != identity) { result = !identity; break; }
                    if (!known) result.reset();
                }
                break;
            }
            case Kind::Implies:
                if (children.size() >= 2) {
                    result = false;
                    for (size_t index = 0; index < children.size(); ++index) {
                        const auto known = value(children[index]);
                        const bool consequent = index + 1 == children.size();
                        if (known && *known == consequent) { result = true; break; }
                        if (!known) result.reset();
                    }
                }
                break;
            case Kind::Xor: {
                if (children.size() < 2) break;
                result = false;
                for (auto child : children) {
                    const auto known = value(child);
                    if (!known) { result.reset(); break; }
                    result = *result != *known;
                }
                break;
            }
            case Kind::Ite:
                if (children.size() == 3) {
                    if (auto condition = value(children[0])) result = value(children[*condition ? 1 : 2]);
                    else if (value(children[1]) == value(children[2])) result = value(children[1]);
                }
                break;
            case Kind::Eq: case Kind::Distinct:
                if (children.size() >= 2) {
                    result = true;
                    for (size_t i = 0; i < children.size(); ++i) {
                        const auto left = value(children[i]);
                        for (size_t j = 0; j < i; ++j) {
                            const auto right = value(children[j]);
                            if (!left || !right) { result.reset(); continue; }
                            if ((*left == *right) != (term.kind == Kind::Eq)) {
                                result = false;
                                break;
                            }
                        }
                        if (result == Truth(false)) break;
                    }
                }
                break;
            default:
                break;
        }
        values_.emplace(id, result);
    }
    return value(root);
}

} // namespace xolver
