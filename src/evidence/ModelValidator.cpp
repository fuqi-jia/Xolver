#include "evidence/ModelValidator.h"
#include <vector>

namespace xolver {

bool ModelValidator::validate(const NativeTerms& ir, const BoolAssignment& assignment) {
    for (ExprId root : ir.assertions())
        if (evalKnown(root, ir, assignment) != std::optional<bool>(true)) return false;
    return true;
}

bool ModelValidator::eval(ExprId root, const NativeTerms& ir, const BoolAssignment& assignment) {
    return evalKnown(root, ir, assignment) == std::optional<bool>(true);
}

std::optional<bool> ModelValidator::evalKnown(
    ExprId root, const NativeTerms& ir, const BoolAssignment& assignment) {
    using Truth = std::optional<bool>;
    std::unordered_map<ExprId, Truth> memo;
    auto val = [&](ExprId id) -> Truth {
        auto it = memo.find(id);
        return it == memo.end() ? std::nullopt : it->second;
    };
    struct Frame { ExprId id; bool processed; };
    std::vector<Frame> stack{{root, false}};
    while (!stack.empty()) {
        auto& frame = stack.back();
        ExprId id = frame.id;
        if (id >= ir.size() || memo.count(id)) { stack.pop_back(); continue; }
        const auto& e = ir.get(id);
        if (!frame.processed) {
            frame.processed = true;
            for (ExprId c : e.children)
                if (c < ir.size() && !memo.count(c)) stack.push_back({c, false});
            continue;
        }
        stack.pop_back();
        Truth r;
        switch (e.kind) {
            case Kind::ConstBool:
                if (auto b = std::get_if<bool>(&e.payload.value)) r = *b;
                break;
            case Kind::Variable: {
                if (auto kind = ir.sortKind(e.sort); kind && *kind != SortKind::Bool) break;
                auto it = assignment.find(id);
                r = it == assignment.end() ? false : it->second;
                break;
            }
            case Kind::Not:
                if (e.children.size() == 1)
                    if (auto a = val(e.children[0])) r = !*a;
                break;
            case Kind::And: case Kind::Or: {
                const bool identity = e.kind == Kind::And;
                r = identity;
                for (ExprId c : e.children) {
                    auto a = val(c);
                    if (a && *a != identity) { r = !identity; break; }
                    if (!a) r = std::nullopt;
                }
                break;
            }
            case Kind::Implies:
                if (e.children.size() == 2) {
                    auto a = val(e.children[0]), b = val(e.children[1]);
                    if ((a && !*a) || (b && *b)) r = true;
                    else if (a && b) r = false;
                }
                break;
            case Kind::Xor:
                if (e.children.size() == 2) {
                    auto a = val(e.children[0]), b = val(e.children[1]);
                    if (a && b) r = *a != *b;
                }
                break;
            case Kind::Ite:
                if (e.children.size() == 3) {
                    auto c = val(e.children[0]);
                    if (c) r = val(e.children[*c ? 1 : 2]);
                    else if (val(e.children[1]) == val(e.children[2])) r = val(e.children[1]);
                }
                break;
            case Kind::Eq: case Kind::Distinct:
                if (e.children.size() >= 2) {
                    r = true;
                    for (size_t i = 0; i < e.children.size(); ++i) {
                        auto a = val(e.children[i]);
                        for (size_t j = 0; j < i; ++j) {
                            auto b = val(e.children[j]);
                            if (!a || !b) { r = std::nullopt; continue; }
                            if ((*a == *b) != (e.kind == Kind::Eq)) {
                                r = false;
                                break;
                            }
                        }
                        if (r && !*r) break;
                    }
                }
                break;
            default: break;
        }
        memo.emplace(id, r);
    }
    return val(root);
}

} // namespace xolver
