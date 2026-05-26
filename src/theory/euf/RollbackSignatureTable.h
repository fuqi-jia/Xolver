#pragma once
#include "theory/euf/EufTypes.h"
#include "theory/euf/EufTermManager.h"
#include <unordered_map>
#include <vector>
#include <optional>
#include <cstdint>

namespace zolver {

struct AppSignature {
    FuncSymbolId symbol;
    std::vector<EClassId> argReps;

    bool operator==(const AppSignature& o) const {
        return symbol == o.symbol && argReps == o.argReps;
    }
};

struct AppSignatureHash {
    std::size_t operator()(const AppSignature& k) const {
        std::size_t h = std::hash<FuncSymbolId>{}(k.symbol);
        for (EClassId c : k.argReps) {
            h ^= std::hash<EClassId>{}(c) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

class RollbackSignatureTable {
public:
    std::optional<EufTermId> find(const AppSignature& sig) const;
    void insertOrAssign(const AppSignature& sig, EufTermId owner);
    void eraseIfOwner(const AppSignature& sig, EufTermId owner);
    size_t snapshot() const;
    void rollback(size_t snap);
    void clear();

    // Debug-only: expose internal table for invariant checking
    const std::unordered_map<AppSignature, EufTermId, AppSignatureHash>& internalTable() const {
        return table_;
    }

private:
    enum class ChangeKind { InsertNew, Overwrite, Erase };
    struct Change {
        ChangeKind kind;
        AppSignature sig;
        std::optional<EufTermId> previousOwner;
    };
    std::unordered_map<AppSignature, EufTermId, AppSignatureHash> table_;
    std::vector<Change> trail_;
};

} // namespace zolver
