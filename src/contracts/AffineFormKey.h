#pragma once

#include "contracts/LinearFormKey.h"
#include <cstddef>

namespace xolver {

// Exact identity for a normalized coefficient vector and rational offset.
// Callers supply sorted terms and a consistent sign convention.
struct AffineFormKey {
    LinearFormKey lhs;
    mpq_class rhs;

    bool operator==(const AffineFormKey& other) const {
        return lhs == other.lhs && rhs == other.rhs;
    }
};

struct AffineFormKeyView {
    const LinearFormKey& lhs;
    const mpq_class& rhs;
};

struct AffineFormKeyHash {
    using is_transparent = void;

    std::size_t operator()(const AffineFormKey& key) const {
        return (*this)(AffineFormKeyView{key.lhs, key.rhs});
    }
    std::size_t operator()(AffineFormKeyView key) const {
        std::size_t hash = LinearFormKeyHash{}(key.lhs);
        hash ^= MpqHash{}(key.rhs) + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        return hash;
    }
};

struct AffineFormKeyEqual {
    using is_transparent = void;

    bool operator()(const AffineFormKey& a, const AffineFormKey& b) const {
        return a == b;
    }
    bool operator()(const AffineFormKey& a, AffineFormKeyView b) const {
        return a.lhs == b.lhs && a.rhs == b.rhs;
    }
    bool operator()(AffineFormKeyView a, const AffineFormKey& b) const {
        return (*this)(b, a);
    }
};

} // namespace xolver
