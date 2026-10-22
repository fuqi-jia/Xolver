#pragma once

#include "contracts/TheorySolver.h"
#include "contracts/TheoryPropagatorCallbacks.h"
#include <unordered_set>
#include <deque>

namespace xolver {

// Theory-lemma dedup layer. `emitted_` prevents a theory re-emitting the same
// lemma; `installed_` tracks lemmas physically handed to CaDiCaL. Both are pure
// SKIP caches — CaDiCaL owns the real learned-clause store.
//
// XOLVER_SAT_LEMMA_MGMT is an entry capacity: bound each dedup cache with FIFO
// eviction so memory stays bounded on huge benchmarks. Evicting an entry only
// makes the corresponding lemma re-derivable/re-emittable on demand (the theory
// re-proves it; re-feeding CaDiCaL a clause it may already hold is sound, just
// redundant). It NEVER drops a clause the proof depends on. Missing or zero
// capacity means unbounded; a true token selects a capacity of 100000.
class TheoryLemmaDatabase : public TheoryLemmaStorage {
public:
    bool contains(const TheoryLemma& lemma) const override;
    bool insertIfNew(const TheoryLemma& lemma) override;
    bool isInstalled(const TheoryLemma& lemma) const override;
    void markInstalled(const TheoryLemma& lemma) override;

private:
    // Hashes select buckets only. Equality compares the complete canonical
    // clause so a collision cannot suppress a distinct theory obligation.
    using Key = std::vector<uint64_t>;
    struct KeyHash {
        size_t operator()(const Key& key) const;
    };
    using KeySet = std::unordered_set<Key, KeyHash>;
    KeySet emitted_;
    KeySet installed_;
    // FIFO order for eviction. Invariant (insert/evict move in lockstep):
    // |fifo| == |set|, the fifo lists present keys in insertion order, so each
    // key appears at most once.
    std::deque<Key> emittedFifo_;
    std::deque<Key> installedFifo_;

    bool mgmtChecked_ = false;
    size_t cap_ = 0;  // 0 == unbounded; ensureMgmt() loads the configured capacity.
    void ensureMgmt();
    void evictIfNeeded(KeySet& set, std::deque<Key>& fifo);

    static Key computeKey(const TheoryLemma& lemma);
};

} // namespace xolver
