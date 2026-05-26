#include "theory/euf/RollbackUnionFind.h"
#include <cassert>

namespace zolver {

EClassId RollbackUnionFind::addNode() {
    EClassId id = static_cast<EClassId>(parent_.size());
    parent_.push_back(id);
    size_.push_back(1);
    return id;
}

EClassId RollbackUnionFind::find(EClassId x) const {
    assert(x < parent_.size());
    while (parent_[x] != x) {
        x = parent_[x];
    }
    return x;
}

bool RollbackUnionFind::same(EClassId a, EClassId b) const {
    if (a >= parent_.size() || b >= parent_.size()) return false;
    return find(a) == find(b);
}

RollbackUnionFind::UniteResult RollbackUnionFind::unite(EClassId a, EClassId b) {
    EClassId ra = find(a);
    EClassId rb = find(b);

    if (ra == rb) {
        return {false, ra, rb};
    }

    // union-by-size: larger becomes winner
    if (size_[ra] < size_[rb]) {
        std::swap(ra, rb);
    }

    trail_.push_back({rb, ra, size_[ra]});
    parent_[rb] = ra;
    size_[ra] += size_[rb];

    return {true, ra, rb};
}

size_t RollbackUnionFind::snapshot() const {
    return trail_.size();
}

void RollbackUnionFind::rollback(size_t snap) {
    while (trail_.size() > snap) {
        auto ch = trail_.back();
        trail_.pop_back();
        parent_[ch.childRoot] = ch.childRoot;
        size_[ch.parentRoot] = ch.oldParentSize;
    }
}

uint32_t RollbackUnionFind::classSize(EClassId root) const {
    EClassId r = find(root);
    return size_[r];
}

} // namespace zolver
