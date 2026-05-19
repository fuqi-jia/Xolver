#pragma once

#include <gmpxx.h>
#include <string>
#include <vector>
#include <functional>

namespace nlcolver {

// ============================================================================
// LinearFormKey: canonical representation of a linear expression's LHS.
// Contains only variable terms (no constant). Sorted by var name for hashing.
//
// Moved from theory/arith/linear/LinearExpr.h to theory/core/ to break
// the dependency of TheorySolver.h on linear/ module headers.
// ============================================================================
struct LinearFormKey {
    std::vector<std::pair<std::string, mpq_class>> terms;  // sorted by var name

    bool operator==(const LinearFormKey& o) const {
        if (terms.size() != o.terms.size()) return false;
        for (size_t i = 0; i < terms.size(); ++i) {
            if (terms[i].first != o.terms[i].first) return false;
            if (terms[i].second != o.terms[i].second) return false;
        }
        return true;
    }
};

struct LinearFormKeyHash {
    std::size_t operator()(const LinearFormKey& f) const {
        std::size_t h = 0;
        for (const auto& t : f.terms) {
            h ^= std::hash<std::string>{}(t.first) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<std::string>{}(t.second.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

} // namespace nlcolver
