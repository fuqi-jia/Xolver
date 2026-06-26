#pragma once
#include "expr/types.h"
#include "util/SmallVector.h"
#include <vector>
#include <utility>
#include <algorithm>
#include <cassert>

namespace xolver {

// Flat sorted-vector map keyed by a monomial (sorted (VarId,exp) list).
// Canonical form (after canonicalize() / operator[] inserts): entries sorted
// strictly-ascending by key, unique keys, no zero-V entries. Requires V to be
// default-constructible, == comparable, and += accumulable.
template <typename V>
class FlatMonomialMap {
public:
    using Key = SmallVector<std::pair<VarId, int>, 4>;
    using Entry = std::pair<Key, V>;
    using Storage = std::vector<Entry>;
    using const_iterator = typename Storage::const_iterator;
    using const_reverse_iterator = typename Storage::const_reverse_iterator;

    bool empty() const { return v_.empty(); }
    size_t size() const { return v_.size(); }
    void clear() { v_.clear(); }
    void reserve(size_t n) { v_.reserve(n); }

    const_iterator begin() const { return v_.begin(); }
    const_iterator end()   const { return v_.end(); }
    const_reverse_iterator rbegin() const { return v_.rbegin(); }
    const_reverse_iterator rend()   const { return v_.rend(); }
    const Entry& front() const { return v_.front(); }
    const Entry& back()  const { return v_.back(); }

    // Checked lookup (assumes canonical). Precondition: key present; asserts
    // otherwise. Mirrors std::map::at for the const read sites.
    const V& at(const Key& key) const {
        const_iterator it = find(key);
        assert(it != v_.end() && "FlatMonomialMap::at: key not present");
        return it->second;
    }

    // Binary-search lookup (assumes canonical). Returns end() if absent.
    const_iterator find(const Key& key) const {
        auto it = std::lower_bound(v_.begin(), v_.end(), key,
            [](const Entry& e, const Key& kk){ return e.first < kk; });
        if (it != v_.end() && !(key < it->first) && !(it->first < key)) return it;
        return v_.end();
    }

    // Insert-or-accumulate, maintaining canonical order (O(n) shift). For cold
    // paths and the terms_[key]+=coeff idiom; hot build should use append()+canonicalize().
    V& operator[](const Key& key) {
        auto it = std::lower_bound(v_.begin(), v_.end(), key,
            [](const Entry& e, const Key& kk){ return e.first < kk; });
        if (it != v_.end() && !(key < it->first) && !(it->first < key)) return it->second;
        it = v_.insert(it, Entry{key, V()});
        return it->second;
    }

    // Unsorted O(1) append; call canonicalize() before any query/iteration.
    void append(Key key, V val) { v_.emplace_back(std::move(key), std::move(val)); }

    // Sort by key, merge duplicates by += , drop zero-V entries.
    void canonicalize() {
        std::stable_sort(v_.begin(), v_.end(),
            [](const Entry& a, const Entry& b){ return a.first < b.first; });
        size_t w = 0;
        for (size_t r = 0; r < v_.size(); ) {
            Key key = std::move(v_[r].first);
            V acc = std::move(v_[r].second);
            size_t s = r + 1;
            while (s < v_.size() && !(v_[s].first < key) && !(key < v_[s].first)) {
                acc += v_[s].second; ++s;
            }
            if (!(acc == V())) { v_[w].first = std::move(key); v_[w].second = std::move(acc); ++w; }
            r = s;
        }
        v_.resize(w);
    }

    bool operator==(const FlatMonomialMap& o) const { return v_ == o.v_; }
    bool operator!=(const FlatMonomialMap& o) const { return !(v_ == o.v_); }

private:
    Storage v_;
};

} // namespace xolver
