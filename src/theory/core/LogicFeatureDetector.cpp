#include "theory/core/LogicFeatureDetector.h"
#include "expr/ir.h"
#include <iostream>

namespace zolver {

LogicFeatureDetector::LogicFeatureDetector(const CoreIr& ir) : ir_(ir) {}

LogicFeatures LogicFeatureDetector::detect() const {
    LogicFeatures f;
    std::unordered_set<ExprId> visited;

    for (ExprId aid : ir_.assertions()) {
        scanExpr(aid, f, visited);
    }

    if (f.hasIntVar && f.hasRealVar) {
        f.hasMixedIntReal = true;
    }

    // Quantifiers, FP, and BV are currently unsupported for sound solving.
    // Arrays are supported in the array logics (QF_AX, ...); the per-logic
    // gate in Solver.cpp decides whether `hasArray` is acceptable, so we do
    // NOT fold it into `hasUnsupported` here.
    if (f.hasQuantifier || f.hasFP || f.hasBV) {
        f.hasUnsupported = true;
    }

    return f;
}

bool LogicFeatureDetector::isNonConstantExpr(ExprId id, const std::unordered_set<ExprId>& visited) const {
    if (id >= ir_.size()) return false;
    const auto& e = ir_.get(id);
    if (e.isConst()) return false;
    if (e.kind == Kind::Variable) return true;
    // Any composite expr that is not a constant is non-constant.
    // For safety, if not visited we conservatively say non-constant.
    if (visited.find(id) == visited.end()) return true;
    return true;
}

void LogicFeatureDetector::scanExpr(ExprId root, LogicFeatures& f, std::unordered_set<ExprId>& visited) const {
    // Iterative DFS (was recursive on children; deep formulas overflowed the
    // stack). Feature flags accumulate order-independently and `visited` dedups
    // the DAG, so traversal order is irrelevant — behavior-identical.
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
    ExprId id = stack.back();
    stack.pop_back();
    if (id >= ir_.size()) continue;
    if (!visited.insert(id).second) continue;

    const auto& e = ir_.get(id);


    // Detect sort-based features for variables
    if (e.kind == Kind::Variable) {
        // Skip solver-internal/synthetic variables (e.g. ITE-lowering aux
        // "__nlc_ite_*"): their sort is an artifact of lowering — an ITE over
        // Real branches can be assigned an Int-sorted aux — not part of the
        // user's declared logic. The mismatch guard must reflect the USER's
        // formula, so a genuine (declare-fun x () Int) in QF_LRA is still
        // flagged, while spurious synthetic Int aux are not.
        bool synthetic = std::holds_alternative<std::string>(e.payload.value) &&
                         std::get<std::string>(e.payload.value).rfind("__", 0) == 0;
        auto sk = ir_.sortKind(e.sort);
        if (sk && !synthetic) {
            switch (*sk) {
                case SortKind::Bool:  f.hasBool = true; break;
                case SortKind::Int:   f.hasInt = true; f.hasIntVar = true; break;
                case SortKind::Real:  f.hasReal = true; f.hasRealVar = true; break;
                case SortKind::BV:    f.hasBV = true; break;
                case SortKind::FP:    f.hasFP = true; break;
                case SortKind::Array: f.hasArray = true; break;
                default: break;
            }
        }
    }

    // Detect kind-based features
    switch (e.kind) {
        case Kind::ConstBool:
            f.hasBool = true;
            break;
        case Kind::ConstInt:
            f.hasInt = true;
            break;
        case Kind::ConstReal: {
            auto sk = ir_.sortKind(e.sort);
            if (sk == SortKind::Int) {
                f.hasInt = true;
            } else if (sk == SortKind::Real) {
                f.hasReal = true;
            } else {
                // SK_INTOREAL or unregistered sort: inspect payload string.
                // Integer literals (no '.' and no '/') → Int, otherwise → Real.
                bool isIntLit = false;
                if (std::holds_alternative<std::string>(e.payload.value)) {
                    const std::string& s = std::get<std::string>(e.payload.value);
                    bool hasDot = s.find('.') != std::string::npos;
                    bool hasSlash = s.find('/') != std::string::npos;
                    if (!hasDot && !hasSlash) {
                        isIntLit = true;
                    }
                }
                if (isIntLit) f.hasInt = true;
                else f.hasReal = true;
            }
            break;
        }
        case Kind::ConstFP:
            f.hasFP = true;
            break;
        case Kind::ConstBV:
            f.hasBV = true;
            break;
        case Kind::UFApply:
            f.hasUF = true;
            break;
        case Kind::Not:
        case Kind::And:
        case Kind::Or:
        case Kind::Implies:
        case Kind::Xor:
            f.hasBool = true;
            break;
        case Kind::Add:
        case Kind::Sub:
        case Kind::Neg:
        case Kind::Mod:
        case Kind::Abs:
            f.hasInterpretedArithmetic = true;
            break;
        case Kind::Pow:
            f.hasNonlinear = true;
            f.hasInterpretedArithmetic = true;
            if (e.children.size() >= 1) {
                auto sk = ir_.sortKind(ir_.get(e.children[0]).sort);
                if (sk == SortKind::Int) f.hasInt = true;
                else if (sk == SortKind::Real) f.hasReal = true;
            }
            break;
        case Kind::Mul: {
            f.hasInterpretedArithmetic = true;
            if (e.children.size() >= 2) {
                bool leftNonConst = isNonConstantExpr(e.children[0], visited);
                bool rightNonConst = isNonConstantExpr(e.children[1], visited);
                if (leftNonConst && rightNonConst) {
                    f.hasNonlinear = true;
                }
            }
            break;
        }
        case Kind::Div: {
            // Integer div vs real div: use sort of result
            f.hasInterpretedArithmetic = true;
            auto sk = ir_.sortKind(e.sort);
            if (sk == SortKind::Int) {
                f.hasInt = true;
            } else {
                f.hasReal = true;
            }
            break;
        }
        case Kind::Forall:
        case Kind::Exists:
            f.hasQuantifier = true;
            break;
        case Kind::BvNot:
        case Kind::BvAnd:
        case Kind::BvOr:
        case Kind::BvAdd:
        case Kind::BvMul:
            f.hasBV = true;
            break;
        case Kind::ToReal:
            f.hasInterpretedArithmetic = true;
            break;  // child pushed by the generic loop below; ToReal is not an atom
        case Kind::ToInt:
        case Kind::IsInt:
            f.hasInterpretedArithmetic = true;
            f.hasUnsupported = true;
            break;
        case Kind::Select:
        case Kind::Store:
        case Kind::ConstArray:
            f.hasArray = true;
            break;
        default:
            break;
    }

    // Propagate sort features from arithmetic relations
    if (e.isAtom() && e.children.size() >= 2) {
        auto sk = ir_.sortKind(ir_.get(e.children[0]).sort);
        if (sk == SortKind::Int) f.hasInt = true;
        else if (sk == SortKind::Real) f.hasReal = true;
        if (e.kind == Kind::Lt || e.kind == Kind::Leq ||
            e.kind == Kind::Gt || e.kind == Kind::Geq) {
            f.hasInterpretedArithmetic = true;
        }
    }

    // Push children (iterative DFS).
    for (ExprId child : e.children) {
        stack.push_back(child);
    }
    }  // while
}

} // namespace zolver
