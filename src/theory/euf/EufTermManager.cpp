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

EufTermId EufTermManager::intern(ExprId eid, const CoreIr& ir) {
    if (eid == TrueSentinelExpr) return internTrueConstant();
    if (eid == FalseSentinelExpr) return internFalseConstant();

    auto it = exprToTerm_.find(eid);
    if (it != exprToTerm_.end()) return it->second;

    const CoreExpr& e = ir.get(eid);
    EufTermId result = NullEufTerm;

    if (e.kind == Kind::ConstBool) {
        bool val = std::get<bool>(e.payload.value);
        result = val ? internTrueConstant() : internFalseConstant();
    } else if (e.kind == Kind::Variable) {
        std::string name = std::get<std::string>(e.payload.value);
        FuncSymbolId sym = internSymbol(name, {}, e.sort);
        result = createNode(sym, {}, e.sort, eid);
    } else if (e.kind == Kind::UFApply) {
        std::string name = std::get<std::string>(e.payload.value);
        std::vector<EufTermId> args;
        std::vector<SortId> argSorts;
        args.reserve(e.children.size());
        argSorts.reserve(e.children.size());
        for (ExprId cid : e.children) {
            EufTermId arg = intern(cid, ir);
            if (arg == NullEufTerm) {
                exprToTerm_[eid] = NullEufTerm;
                return NullEufTerm;
            }
            args.push_back(arg);
            argSorts.push_back(ir.get(cid).sort);
        }
        FuncSymbolId sym = internSymbol(name, argSorts, e.sort);
        result = createNode(sym, args, e.sort, eid);
    } else {
        // Anything else (Add, Sub, etc.) -> NullEufTerm
        result = NullEufTerm;
    }

    exprToTerm_[eid] = result;
    return result;
}

} // namespace nlcolver
