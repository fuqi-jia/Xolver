#pragma once

#include "expr/payload.h"
#include "expr/types.h"
#include "expr/Datatype.h"
#include "util/SmallVector.h"
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <optional>

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
    // the CoreExpr payload string; the DatatypeRegistry resolves it.
    Constructor, Selector, Tester,
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

    // Hash-cons deduplication is UNCONDITIONAL. Identical
    // (kind, sort, children, payload) tuples collapse to the same ExprId.
    // Critical for theory-level SAT-lit unification: equivalent
    // sub-expressions emitted by separate passes (e.g. lemma generators
    // vs the parsed assertion) must share ExprIds so the atomizer
    // assigns them a single SAT lit. Without it, algebraically equivalent
    // atoms become distinct Boolean variables and CDCL cannot propagate
    // between them — see commit message of `nia newton: iter-60` for the
    // diagnosis evidence (eid=37 vs eid=19 for the same `(< X (* (+ V 1) (+ V 1)))`).
    ExprId add(CoreExpr e) {
        ConsKey key{e.kind, e.sort, e.children, e.payload.value};
        auto it = consMap_.find(key);
        if (it != consMap_.end()) return it->second;
        ExprId id = static_cast<ExprId>(exprs_.size());
        exprs_.push_back(std::move(e));
        consMap_.emplace(std::move(key), id);
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

    // Array sort parameters: (Array index elem). SortId is otherwise opaque to
    // the index/element sorts, which the array theory and model output need.
    void registerArraySort(SortId arr, SortId index, SortId elem) {
        arraySortParams_[arr] = {index, elem};
    }
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

    // Generate a globally unique fresh variable name and add it to the IR.
    // Guarantees:
    //   1. Name does not collide with any existing Variable node in exprs_
    //   2. Name does not collide with any previously generated fresh name
    //   3. Returns a newly added ExprId (never reuses existing node)
    ExprId makeFreshVariable(SortId sort, std::string_view prefix) {
        std::string name;
        do {
            name = std::string(prefix) + "_" + std::to_string(freshVarCounter_++);
        } while (nameCollides(name));
        freshVarNames_.insert(name);
        CoreExpr e;
        e.kind = Kind::Variable;
        e.sort = sort;
        e.payload = Payload(std::move(name));
        return add(std::move(e));
    }

private:
    bool nameCollides(const std::string& name) const {
        // Check against existing variable nodes in exprs_
        for (ExprId id = 0; id < static_cast<ExprId>(exprs_.size()); ++id) {
            const auto& node = exprs_[id];
            if (node.kind == Kind::Variable) {
                if (auto* s = std::get_if<std::string>(&node.payload.value)) {
                    if (*s == name) return true;
                }
            }
        }
        // Check against previously generated fresh names
        if (freshVarNames_.count(name)) return true;
        return false;
    }
    // Hash-cons key used by add().
    struct ConsKey {
        Kind kind;
        SortId sort;
        SmallVector<ExprId, 4> children;
        Payload::Value payload;
        bool operator==(const ConsKey& o) const {
            return kind == o.kind && sort == o.sort &&
                   children == o.children && payload == o.payload;
        }
    };
    struct ConsKeyHash {
        std::size_t operator()(const ConsKey& k) const {
            std::size_t h = std::hash<uint16_t>{}(static_cast<uint16_t>(k.kind));
            h ^= std::hash<uint32_t>{}(k.sort) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            for (ExprId c : k.children)
                h ^= std::hash<uint32_t>{}(c) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            std::size_t ph = 0;
            if (auto* b = std::get_if<bool>(&k.payload)) ph = std::hash<bool>{}(*b);
            else if (auto* i = std::get_if<int64_t>(&k.payload)) ph = std::hash<int64_t>{}(*i);
            else if (auto* s = std::get_if<std::string>(&k.payload)) ph = std::hash<std::string>{}(*s);
            else if (auto* u = std::get_if<uint64_t>(&k.payload)) ph = std::hash<uint64_t>{}(*u);
            h ^= ph + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            return h;
        }
    };

    std::unordered_map<ConsKey, ExprId, ConsKeyHash> consMap_;
    std::vector<CoreExpr> exprs_;
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
};

} // namespace xolver
