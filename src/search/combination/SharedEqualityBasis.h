#pragma once

#include "ir/types.h"
#include <cstddef>
#include <unordered_map>
#include <utility>

namespace xolver {

// Select a spanning forest from proved equalities within one theory check.
// A skipped edge follows by transitivity from retained edges. Each retained
// edge still needs its own explanation and normal SAT installation protocol.
// Rebuild this selection when the source facts or their explanations change.
class SharedEqualityBasis {
public:
    bool insert(SharedTermId a, SharedTermId b) {
        if (a == b) return false;
        a = representative(a);
        b = representative(b);
        if (a == b) return false;
        if (nodes_.at(a).size < nodes_.at(b).size) std::swap(a, b);
        nodes_.at(b).parent = a;
        nodes_.at(a).size += nodes_.at(b).size;
        return true;
    }

private:
    struct Node {
        SharedTermId parent;
        size_t size;
    };
    std::unordered_map<SharedTermId, Node> nodes_;

    SharedTermId representative(SharedTermId term) {
        nodes_.try_emplace(term, Node{term, 1});
        SharedTermId root = term;
        while (nodes_.at(root).parent != root) root = nodes_.at(root).parent;
        while (term != root) {
            const SharedTermId next = nodes_.at(term).parent;
            nodes_.at(term).parent = root;
            term = next;
        }
        return root;
    }
};

} // namespace xolver
