#pragma once
#include "theory/euf/EufTypes.h"
#include "expr/ir.h"
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>

namespace xolver {

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
    EufTermId internConstant(const std::string& name, SortId sort);

    const std::vector<EufTermId>& parentsOf(EufTermId t) const {
        static const std::vector<EufTermId> empty;
        return t < parents_.size() ? parents_[t] : empty;
    }

    // O(1) reverse lookup (was an O(#symbols) linear scan over symbols_).
    const std::string& symbolName(FuncSymbolId sym) const;

    // True iff any "#builtin.*" function symbol has been interned. Lets the
    // EUF saturation loop skip constant-folding work entirely in problems that
    // have no arithmetic builtins (e.g. pure QF_UF), where it can never fire.
    bool hasBuiltinSymbols() const { return hasBuiltinSymbols_; }

private:
    std::vector<ENode> nodes_;
    std::unordered_map<FuncSymbolKey, FuncSymbolId, FuncSymbolKeyHash> symbols_;
    // Dense reverse index: symbolNames_[id] == that symbol's name.
    std::vector<std::string> symbolNames_;
    bool hasBuiltinSymbols_ = false;
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

} // namespace xolver
