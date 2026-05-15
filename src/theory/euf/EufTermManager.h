#pragma once
#include "theory/euf/EufTypes.h"
#include "expr/ir.h"
#include <string>
#include <vector>
#include <unordered_map>

namespace nlcolver {

struct ENode {
    EufTermId id;
    FuncSymbolId symbol;
    std::vector<EufTermId> args;
    SortId sort;
    ExprId origin;
};

struct FuncSymbolKey {
    std::string name;
    std::vector<SortId> argSorts;
    SortId resultSort;
    bool operator==(const FuncSymbolKey& o) const {
        return name == o.name && argSorts == o.argSorts && resultSort == o.resultSort;
    }
};

struct FuncSymbolKeyHash {
    std::size_t operator()(const FuncSymbolKey& k) const {
        std::size_t h = std::hash<std::string>{}(k.name);
        for (SortId s : k.argSorts) {
            h ^= std::hash<SortId>{}(s) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        h ^= std::hash<SortId>{}(k.resultSort) + 0x9e3779b9 + (h << 6) + (h >> 2);
        return h;
    }
};

struct TermKey {
    FuncSymbolId symbol;
    std::vector<EufTermId> args;
    bool operator==(const TermKey& o) const {
        return symbol == o.symbol && args == o.args;
    }
};

struct TermKeyHash {
    std::size_t operator()(const TermKey& k) const {
        std::size_t h = std::hash<FuncSymbolId>{}(k.symbol);
        for (EufTermId a : k.args) {
            h ^= std::hash<EufTermId>{}(a) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

class EufTermManager {
public:
    EufTermManager() = default;

    EufTermId intern(ExprId eid, const CoreIr& ir);
    const ENode& node(EufTermId id) const { return nodes_[id]; }
    bool isApplication(EufTermId id) const {
        return id < nodes_.size() && !nodes_[id].args.empty();
    }
    size_t termCount() const { return nodes_.size(); }
    void clear();

    EufTermId trueConstant() const { return trueConstant_; }
    EufTermId falseConstant() const { return falseConstant_; }
    EufTermId internTrueConstant();
    EufTermId internFalseConstant();

    const std::vector<EufTermId>& parentsOf(EufTermId t) const {
        static const std::vector<EufTermId> empty;
        return t < parents_.size() ? parents_[t] : empty;
    }

private:
    std::vector<ENode> nodes_;
    std::unordered_map<FuncSymbolKey, FuncSymbolId, FuncSymbolKeyHash> symbols_;
    std::unordered_map<TermKey, EufTermId, TermKeyHash> termMap_;
    std::unordered_map<ExprId, EufTermId> exprToTerm_;

    std::vector<std::vector<EufTermId>> parents_;

    EufTermId trueConstant_ = NullEufTerm;
    EufTermId falseConstant_ = NullEufTerm;

    FuncSymbolId internSymbol(const std::string& name,
                              const std::vector<SortId>& argSorts,
                              SortId resultSort);
    EufTermId createNode(FuncSymbolId sym,
                         const std::vector<EufTermId>& args,
                         SortId sort,
                         ExprId origin);
};

} // namespace nlcolver
