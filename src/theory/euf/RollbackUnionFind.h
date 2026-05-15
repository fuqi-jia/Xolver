#pragma once
#include "theory/euf/EufTypes.h"
#include <vector>
#include <cstdint>

namespace nlcolver {

class RollbackUnionFind {
public:
    EClassId addNode();
    EClassId find(EClassId x) const;
    bool same(EClassId a, EClassId b) const;

    struct UniteResult {
        bool merged;
        EClassId winner;
        EClassId loser;
    };
    UniteResult unite(EClassId a, EClassId b);

    size_t snapshot() const;
    void rollback(size_t snap);
    uint32_t classSize(EClassId root) const;
    size_t size() const { return parent_.size(); }

private:
    std::vector<EClassId> parent_;
    std::vector<uint32_t> size_;
    struct Change {
        EClassId childRoot;
        EClassId parentRoot;
        uint32_t oldParentSize;
    };
    std::vector<Change> trail_;
};

} // namespace nlcolver
