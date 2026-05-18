#include "theory/euf/EufTermManager.h"
#include <cassert>
#include <algorithm>

namespace nlcolver {

void EufTermManager::clear() {
    nodes_.clear();
    symbols_.clear();
    termMap_.clear();
    exprToTerm_.clear();
    parents_.clear();
    trueConstant_ = NullEufTerm;
    falseConstant_ = NullEufTerm;

}

FuncSymbolId EufTermManager::internSymbol(const std::string& name,
                                          const std::vector<SortId>& argSorts,
                                          SortId resultSort) {
    FuncSymbolKey key{name, argSorts, resultSort};
    auto it = symbols_.find(key);
    if (it != symbols_.end()) return it->second;
    FuncSymbolId id = static_cast<FuncSymbolId>(symbols_.size());
    symbols_.emplace(std::move(key), id);
    return id;
}

EufTermId EufTermManager::createNode(FuncSymbolId sym,
                                     const std::vector<EufTermId>& args,
                                     SortId sort,
                                     ExprId origin) {
    TermKey key{sym, args};
    auto it = termMap_.find(key);
    if (it != termMap_.end()) return it->second;

    EufTermId id = static_cast<EufTermId>(nodes_.size());
    nodes_.push_back(ENode{id, sym, args, sort, origin});
    termMap_.emplace(std::move(key), id);

    // Populate parent use-lists
    if (parents_.size() <= id) {
        parents_.resize(id + 1);
    }
    for (EufTermId arg : args) {
        if (arg < parents_.size()) {
            parents_[arg].push_back(id);
        }
    }

    return id;
}

EufTermId EufTermManager::internTrueConstant() {
    if (trueConstant_ != NullEufTerm) return trueConstant_;
    FuncSymbolId sym = internSymbol("true", {}, NullSort);
    trueConstant_ = createNode(sym, {}, NullSort, TrueSentinelExpr);
    return trueConstant_;
}

EufTermId EufTermManager::internFalseConstant() {
    if (falseConstant_ != NullEufTerm) return falseConstant_;
    FuncSymbolId sym = internSymbol("false", {}, NullSort);
    falseConstant_ = createNode(sym, {}, NullSort, FalseSentinelExpr);
    return falseConstant_;
}


EufTermId EufTermManager::intern(ExprId root, const CoreIr& ir) {
    if (root == TrueSentinelExpr) return internTrueConstant();
    if (root == FalseSentinelExpr) return internFalseConstant();

    auto it = exprToTerm_.find(root);
    if (it != exprToTerm_.end()) return it->second;

    struct Frame {
        ExprId eid;
        bool childrenDone;
    };

    std::vector<Frame> stack;
    std::unordered_map<ExprId, EufTermId> done;

    auto tryResolve = [&](ExprId eid) -> bool {
        if (eid == TrueSentinelExpr) {
            done[eid] = internTrueConstant();
            return true;
        }
        if (eid == FalseSentinelExpr) {
            done[eid] = internFalseConstant();
            return true;
        }
        auto git = exprToTerm_.find(eid);
        if (git != exprToTerm_.end()) {
            done[eid] = git->second;
            return true;
        }
        if (done.count(eid)) return true;
        return false;
    };

    auto computeLeaf = [&](ExprId eid) -> EufTermId {
        const CoreExpr& e = ir.get(eid);
        if (e.kind == Kind::ConstBool) {
            bool val = std::get<bool>(e.payload.value);
            return val ? internTrueConstant() : internFalseConstant();
        }
        if (e.kind == Kind::Variable) {
            std::string name = std::get<std::string>(e.payload.value);
            FuncSymbolId sym = internSymbol(name, {}, e.sort);
            return createNode(sym, {}, e.sort, eid);
        }
        if (e.isConst()) {
            std::string name;
            if (auto* b = std::get_if<bool>(&e.payload.value)) {
                name = *b ? "true" : "false";
            } else if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
                name = std::to_string(*i);
            } else if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                name = *s;
            } else if (auto* bv = std::get_if<uint64_t>(&e.payload.value)) {
                name = "bv" + std::to_string(*bv);
            }
            if (!name.empty()) {
                FuncSymbolId sym = internSymbol(name, {}, NullSort);
                return createNode(sym, {}, NullSort, eid);
            }
        }
        return NullEufTerm;
    };

    auto builtinName = [](Kind k) -> std::string {
        switch (k) {
            case Kind::Add:    return "#builtin.Add";
            case Kind::Sub:    return "#builtin.Sub";
            case Kind::Neg:    return "#builtin.Neg";
            case Kind::Mul:    return "#builtin.Mul";
            case Kind::Div:    return "#builtin.Div";
            case Kind::Mod:    return "#builtin.Mod";
            case Kind::Abs:    return "#builtin.Abs";
            case Kind::Pow:    return "#builtin.Pow";
            case Kind::ToInt:  return "#builtin.ToInt";
            case Kind::ToReal: return "#builtin.ToReal";
            default:           return "";
        }
    };

    auto isLeafKind = [](Kind k) -> bool {
        return k == Kind::ConstBool || k == Kind::ConstInt ||
               k == Kind::ConstReal || k == Kind::ConstBV ||
               k == Kind::ConstFP || k == Kind::Variable;
    };

    auto isApplicationKind = [&](Kind k) -> bool {
        return k == Kind::UFApply || !builtinName(k).empty();
    };

    if (!tryResolve(root)) {
        stack.push_back(Frame{root, false});
    }

    while (!stack.empty()) {
        Frame& f = stack.back();
        // Value copy: intern()/createNode() may reallocate CoreIr's exprs_ vector.
        const CoreExpr e = ir.get(f.eid);

        if (!f.childrenDone) {
            f.childrenDone = true;

            // Leaf: compute inline
            if (isLeafKind(e.kind)) {
                EufTermId res = computeLeaf(f.eid);
                exprToTerm_[f.eid] = res;
                done[f.eid] = res;
                stack.pop_back();
                continue;
            }

            // Application (UFApply or interpreted term): need children first
            if (isApplicationKind(e.kind)) {
                for (size_t i = e.children.size(); i-- > 0; ) {
                    if (!tryResolve(e.children[i])) {
                        stack.push_back(Frame{e.children[i], false});
                    }
                }
                continue;
            }

            // Unsupported kind (e.g. Ite, And, Or, Lt, etc.)
            exprToTerm_[f.eid] = NullEufTerm;
            done[f.eid] = NullEufTerm;
            stack.pop_back();
            continue;
        }

        // Second visit: children resolved in `done`
        if (isApplicationKind(e.kind)) {
            std::vector<EufTermId> args;
            std::vector<SortId> argSorts;
            args.reserve(e.children.size());
            argSorts.reserve(e.children.size());
            bool hasNull = false;
            for (ExprId cid : e.children) {
                EufTermId arg = done.at(cid);
                if (arg == NullEufTerm) {
                    hasNull = true;
                    break;
                }
                args.push_back(arg);
                argSorts.push_back(ir.get(cid).sort);
            }
            if (hasNull) {
                exprToTerm_[f.eid] = NullEufTerm;
                done[f.eid] = NullEufTerm;
            } else {
                std::string name;
                if (e.kind == Kind::UFApply) {
                    name = std::get_if<std::string>(&e.payload.value)
                           ? std::get<std::string>(e.payload.value)
                           : "";
                } else {
                    name = builtinName(e.kind);
                }
                FuncSymbolId sym = internSymbol(name, argSorts, e.sort);
                EufTermId res = createNode(sym, args, e.sort, f.eid);
                exprToTerm_[f.eid] = res;
                done[f.eid] = res;
            }
            stack.pop_back();
            continue;
        }

        assert(e.kind != Kind::Ite && "ITE must be lowered by CoreIteLowerer before reaching EUF");

        // Fallback (should not reach here for non-leaf kinds)
        EufTermId res = computeLeaf(f.eid);
        exprToTerm_[f.eid] = res;
        done[f.eid] = res;
        stack.pop_back();
    }

    return done.at(root);
}

} // namespace nlcolver
