#pragma once

#include "expr/payload.h"
#include "expr/types.h"
#include "util/SmallVector.h"
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <optional>

namespace nlcolver {

/**
 * Expression kind.
 * Aligned with SOMTParser NODE_KIND where possible to simplify adapter mapping.
 */
enum class Kind : uint16_t {
    ConstBool, ConstInt, ConstReal, ConstBV, ConstFP,
    Variable,
    UFApply,
    Not, And, Or, Implies, Xor, Ite,
    Add, Sub, Neg, Mul, Div, Mod, Abs, Pow,
    Eq, Distinct, Lt, Leq, Gt, Geq,
    BvNot, BvAnd, BvOr, BvAdd, BvMul,
    Forall, Exists,
    ToInt, ToReal,
    Unknown,
};

/**
 * CoreExpr: lightweight internal IR node.
 *
 * No hash-consing here — SOMTParser's NodeManager already guarantees
 * structural sharing. The FrontendAdapter maintains a memo table
 * Node → ExprId to ensure each SOMTParser node maps to one CoreExpr.
 */
struct CoreExpr {
    Kind kind;
    SortId sort;
    SmallVector<ExprId, 4> children;
    Payload payload;

    bool isLeaf() const { return children.empty(); }
    bool isConst() const {
        return kind == Kind::ConstBool || kind == Kind::ConstInt ||
               kind == Kind::ConstReal || kind == Kind::ConstBV ||
               kind == Kind::ConstFP;
    }
    bool isVar() const { return kind == Kind::Variable; }
    bool isAtom() const {
        return kind == Kind::Eq || kind == Kind::Distinct ||
               kind == Kind::Lt || kind == Kind::Leq ||
               kind == Kind::Gt || kind == Kind::Geq;
    }
};

/**
 * CoreIr: owns all CoreExpr nodes, provides dense indexing.
 *
 * Created by FrontendAdapter via import from SOMTParser AST.
 */
class CoreIr {
public:
    CoreIr() = default;

    // Dense storage
    ExprId add(CoreExpr e) {
        ExprId id = static_cast<ExprId>(exprs_.size());
        exprs_.push_back(std::move(e));
        return id;
    }

    const CoreExpr& get(ExprId id) const { return exprs_[id]; }
    CoreExpr& get(ExprId id) { return exprs_[id]; }
    size_t size() const { return exprs_.size(); }

    // Scope-aware assertions
    void pushScope() { ++currentScope_; }
    void popScope() {
        if (currentScope_ == 0) return;
        --currentScope_;
        // Remove assertions added at scopes > currentScope_
        auto it = std::remove_if(scopedAssertions_.begin(), scopedAssertions_.end(),
            [this](const auto& pair) { return pair.first > currentScope_; });
        scopedAssertions_.erase(it, scopedAssertions_.end());
    }
    void addAssertion(ExprId id) { scopedAssertions_.push_back({currentScope_, id}); }
    void addAssertion(ExprId id, ScopeLevel level) { scopedAssertions_.push_back({level, id}); }
    void clearAssertions() { scopedAssertions_.clear(); }

    std::vector<ExprId> assertions() const {
        std::vector<ExprId> result;
        for (const auto& [level, id] : scopedAssertions_) {
            (void)level; // all remaining are <= currentScope_
            result.push_back(id);
        }
        return result;
    }

    const std::vector<std::pair<ScopeLevel, ExprId>>& getScopedAssertions() const {
        return scopedAssertions_;
    }

    void replaceAssertions(const std::vector<ExprId>& newAssertions) {
        scopedAssertions_.clear();
        for (ExprId id : newAssertions) {
            scopedAssertions_.push_back({currentScope_, id});
        }
    }

    ScopeLevel currentScopeLevel() const { return currentScope_; }

    // Sort kind tracking (populated by FrontendAdapter)
    void registerSort(SortId id, SortKind kind) { sortKinds_[id] = kind; }
    std::optional<SortKind> sortKind(SortId id) const {
        auto it = sortKinds_.find(id);
        if (it != sortKinds_.end()) return it->second;
        return std::nullopt;
    }

    SortId boolSortId() const { return boolSortId_; }
    void setBoolSortId(SortId id) { boolSortId_ = id; }

    SortId intSortId() const { return intSortId_; }
    void setIntSortId(SortId id) { intSortId_ = id; }

    SortId realSortId() const { return realSortId_; }
    void setRealSortId(SortId id) { realSortId_ = id; }

    SortId allocateSortId() { return nextSortId_++; }

private:
    std::vector<CoreExpr> exprs_;
    std::vector<std::pair<ScopeLevel, ExprId>> scopedAssertions_;
    ScopeLevel currentScope_ = 0;
    std::unordered_map<SortId, SortKind> sortKinds_;
    SortId boolSortId_ = NullSort;
    SortId intSortId_ = NullSort;
    SortId realSortId_ = NullSort;
    SortId nextSortId_ = 1;
};

} // namespace nlcolver
