#pragma once

#include "expr/payload.h"
#include "expr/types.h"
#include "util/SmallVector.h"
#include <vector>
#include <algorithm>

namespace nlcolver {

/**
 * Expression kind.
 * Aligned with SOMTParser NODE_KIND where possible to simplify adapter mapping.
 */
enum class Kind : uint16_t {
    ConstBool, ConstInt, ConstReal, ConstBV, ConstFP,
    Variable,
    Not, And, Or, Implies, Xor, Ite,
    Add, Sub, Neg, Mul, Div, Mod, Abs, Pow,
    Eq, Distinct, Lt, Leq, Gt, Geq,
    BvNot, BvAnd, BvOr, BvAdd, BvMul,
    Forall, Exists,
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

    std::vector<ExprId> assertions() const {
        std::vector<ExprId> result;
        for (const auto& [level, id] : scopedAssertions_) {
            (void)level; // all remaining are <= currentScope_
            result.push_back(id);
        }
        return result;
    }

    ScopeLevel currentScopeLevel() const { return currentScope_; }

private:
    std::vector<CoreExpr> exprs_;
    std::vector<std::pair<ScopeLevel, ExprId>> scopedAssertions_;
    ScopeLevel currentScope_ = 0;
};

} // namespace nlcolver
