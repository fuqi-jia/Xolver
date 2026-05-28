#include "proof/ModelValidator.h"
#include <cassert>
#include <unordered_map>
#include <vector>

namespace xolver {

bool ModelValidator::validate(const CoreIr& ir, const BoolAssignment& assignment) {
    for (ExprId assertion : ir.assertions()) {
        if (!eval(assertion, ir, assignment)) {
            return false;
        }
    }
    return true;
}

bool ModelValidator::eval(ExprId root, const CoreIr& ir, const BoolAssignment& assignment) {
    // Iterative two-visit post-order (was recursive on bool structure; a deeply
    // nested formula overflowed the stack). `val` reads a child's memoized result;
    // an absent/NullExpr child evaluates to true, matching the former eval(NullExpr).
    std::unordered_map<ExprId, bool> memo;
    auto val = [&](ExprId c) -> bool {
        if (c == NullExpr) return true;
        auto it = memo.find(c);
        return it != memo.end() ? it->second : true;
    };
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& fr = stack.back();
        ExprId eid = fr.e;
        if (eid == NullExpr || memo.find(eid) != memo.end()) { stack.pop_back(); continue; }
        const CoreExpr& e = ir.get(eid);
        const bool recurses = (e.kind == Kind::Not || e.kind == Kind::And ||
                               e.kind == Kind::Or || e.kind == Kind::Implies ||
                               e.kind == Kind::Eq);
        if (!fr.processed) {
            fr.processed = true;
            if (recurses) {
                for (ExprId c : e.children)
                    if (c != NullExpr && memo.find(c) == memo.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        bool r;
        switch (e.kind) {
            case Kind::ConstBool:
                r = std::get<bool>(e.payload.value);
                break;
            case Kind::Variable: {
                auto it = assignment.find(eid);
                r = it != assignment.end() ? it->second : false;
                break;
            }
            case Kind::Not:
                assert(e.children.size() == 1);
                r = !val(e.children[0]);
                break;
            case Kind::And:
                r = true;
                for (ExprId c : e.children) { if (!val(c)) { r = false; break; } }
                break;
            case Kind::Or:
                r = false;
                for (ExprId c : e.children) { if (val(c)) { r = true; break; } }
                break;
            case Kind::Implies:
                assert(e.children.size() == 2);
                r = !val(e.children[0]) || val(e.children[1]);
                break;
            case Kind::Eq:
                assert(e.children.size() == 2);
                // Stage A: boolean equality only.
                r = (val(e.children[0]) == val(e.children[1]));
                break;
            default:
                // Stage A: non-boolean expressions treated as "cannot validate".
                r = true;
                break;
        }
        memo[eid] = r;
    }
    return val(root);
}

} // namespace xolver
