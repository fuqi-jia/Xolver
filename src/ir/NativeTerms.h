#pragma once

#include "ir/payload.h"
#include "ir/types.h"
#include "ir/Datatype.h"
#include "base/SmallVector.h"
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <optional>
#include <memory>
#include <string_view>

namespace SOMTParser { class DAGNode; class Sort; class NodeManager; }

namespace xolver {

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
    ToInt, ToReal, IsInt,
    Select, Store, ConstArray,
    // Algebraic datatypes. The constructor/selector/tester NAME is carried in
    // the TermExpr payload string; the DatatypeRegistry resolves it.
    Constructor, Selector, Tester,
    Unknown,
    // Distinct from free symbols: quantifier children are [body, binder...].
    // Binder identity is ExprId, so shadowing never relies on printed names.
    BoundVariable,
};

// Temporary construction/read value. Never retained as an expression graph.
struct TermExpr {
    Kind kind = Kind::Unknown;
    SortId sort = NullSort;
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

// Dense handles into SOMTParser's DAG. This owns query scopes and theory-facing
// metadata, but stores no duplicate expressions or mutable expression views.
class NativeTerms {
public:
    NativeTerms();
    explicit NativeTerms(std::shared_ptr<SOMTParser::NodeManager>);
    ~NativeTerms();
    NativeTerms(NativeTerms&&) noexcept;
    NativeTerms& operator=(NativeTerms&&) noexcept;
    NativeTerms(const NativeTerms&);
    NativeTerms& operator=(const NativeTerms&);

    ExprId add(TermExpr);
    ExprId addShared(TermExpr);
    const TermExpr get(ExprId) const;
    size_t size() const;
    // Index the original DAG by identity, including all reachable children.
    // Let aliases are resolved without duplicating their bound expressions.
    ExprId index(std::shared_ptr<SOMTParser::DAGNode>);
    std::shared_ptr<SOMTParser::DAGNode> native(ExprId) const;
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> native(const std::vector<ExprId>& ids) const {
        std::vector<std::shared_ptr<SOMTParser::DAGNode>> nodes;
        nodes.reserve(ids.size());
        for (auto id : ids) nodes.push_back(native(id));
        return nodes;
    }
    SortId indexSort(std::shared_ptr<SOMTParser::Sort>);
    void registerNativeSort(SortId, std::shared_ptr<SOMTParser::Sort>);

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

    // Restore a query snapshot without allocation, including every assertion's
    // original scope. Preprocessing may replace roots, but must not change the
    // next API query or make root assertions disappear after pop().
    void restoreAssertions(std::vector<std::pair<ScopeLevel, ExprId>>&& saved) noexcept {
        scopedAssertions_.swap(saved);
    }

    void replaceAssertions(const std::vector<ExprId>& newAssertions) {
        scopedAssertions_.clear();
        for (ExprId id : newAssertions) {
            scopedAssertions_.push_back({currentScope_, id});
        }
    }

    ScopeLevel currentScopeLevel() const { return currentScope_; }

    // Sort kind tracking (populated by FrontendAdapter)
    void registerSort(SortId id, SortKind kind);
    std::optional<SortKind> sortKind(SortId id) const {
        auto it = sortKinds_.find(id);
        if (it != sortKinds_.end()) return it->second;
        return std::nullopt;
    }

    // Array sort parameters: (Array index elem). SortId is otherwise opaque to
    // the index/element sorts, which the array theory and model output need.
    void registerArraySort(SortId arr, SortId index, SortId elem);
    std::optional<std::pair<SortId, SortId>> arraySortParams(SortId arr) const {
        auto it = arraySortParams_.find(arr);
        if (it != arraySortParams_.end()) return it->second;
        return std::nullopt;
    }

    // Algebraic-datatype signatures (populated by FrontendAdapter). Const access
    // for the theory layer; mutable accessor for the adapter to populate.
    const DatatypeRegistry& datatypes() const { return datatypes_; }
    DatatypeRegistry& datatypes() { return datatypes_; }
    bool hasDatatypes() const { return !datatypes_.empty(); }

    SortId boolSortId() const { return boolSortId_; }
    void setBoolSortId(SortId id) { boolSortId_ = id; }

    SortId intSortId() const { return intSortId_; }
    void setIntSortId(SortId id) { intSortId_ = id; }

    SortId realSortId() const { return realSortId_; }
    void setRealSortId(SortId id) { realSortId_ = id; }

    SortId allocateSortId() { return nextSortId_++; }

    ExprId makeFreshVariable(SortId sort, std::string_view prefix,
                             bool routingAuxiliary = false);

    bool isInternalVariable(ExprId id) const { return internalVariables_.count(id) != 0; }
    bool isRoutingAuxiliary(ExprId id) const { return routingAuxiliaries_.count(id) != 0; }

private:
    struct Storage;
    std::unique_ptr<Storage> storage_;
    ExprId append(std::shared_ptr<SOMTParser::DAGNode>);
    std::vector<std::pair<ScopeLevel, ExprId>> scopedAssertions_;
    ScopeLevel currentScope_ = 0;
    std::unordered_map<SortId, SortKind> sortKinds_;
    std::unordered_map<SortId, std::pair<SortId, SortId>> arraySortParams_;
    DatatypeRegistry datatypes_;
    SortId boolSortId_ = NullSort;
    SortId intSortId_ = NullSort;
    SortId realSortId_ = NullSort;
    SortId nextSortId_ = 1;

    uint64_t freshVarCounter_ = 0;
    std::unordered_set<std::string> freshVarNames_;
    std::unordered_set<ExprId> internalVariables_;
    std::unordered_set<ExprId> routingAuxiliaries_;
};

} // namespace xolver
