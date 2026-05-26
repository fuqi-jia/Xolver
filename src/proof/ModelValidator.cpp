#include "proof/ModelValidator.h"
#include <cassert>

namespace zolver {

bool ModelValidator::validate(const CoreIr& ir, const BoolAssignment& assignment) {
    for (ExprId assertion : ir.assertions()) {
        if (!eval(assertion, ir, assignment)) {
            return false;
        }
    }
    return true;
}

bool ModelValidator::eval(ExprId eid, const CoreIr& ir, const BoolAssignment& assignment) {
    if (eid == NullExpr) return true;

    const CoreExpr& e = ir.get(eid);
    switch (e.kind) {
        case Kind::ConstBool:
            return std::get<bool>(e.payload.value);
        case Kind::Variable: {
            auto it = assignment.find(eid);
            return it != assignment.end() ? it->second : false;
        }
        case Kind::Not: {
            assert(e.children.size() == 1);
            return !eval(e.children[0], ir, assignment);
        }
        case Kind::And: {
            for (ExprId c : e.children) {
                if (!eval(c, ir, assignment)) return false;
            }
            return true;
        }
        case Kind::Or: {
            for (ExprId c : e.children) {
                if (eval(c, ir, assignment)) return true;
            }
            return false;
        }
        case Kind::Implies: {
            assert(e.children.size() == 2);
            return !eval(e.children[0], ir, assignment) || eval(e.children[1], ir, assignment);
        }
        case Kind::Eq: {
            assert(e.children.size() == 2);
            // Stage A: boolean equality only.
            return eval(e.children[0], ir, assignment) == eval(e.children[1], ir, assignment);
        }
        default:
            // Stage A: non-boolean expressions treated as "cannot validate".
            return true;
    }
}

} // namespace zolver
