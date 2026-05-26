#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <unordered_set>
#include <deque>

namespace zolver {

// Theory-lemma dedup layer. `emitted_` prevents a theory re-emitting the same
// lemma; `installed_` tracks lemmas physically handed to CaDiCaL. Both are pure
// SKIP caches — CaDiCaL owns the real learned-clause store.
//
// ZOLVER_SAT_LEMMA_MGMT (default OFF): bound each dedup cache with FIFO
// eviction so memory stays bounded on huge benchmarks. Evicting an entry only
// makes the corresponding lemma re-derivable/re-emittable on demand (the theory
// re-proves it; re-feeding CaDiCaL a clause it may already hold is sound, just
// redundant). It NEVER drops a clause the proof depends on. Flag OFF => cap 0
// => caches unbounded => behavior identical to before.
class TheoryLemmaDatabase : public TheoryLemmaStorage {
public:
    bool contains(const TheoryLemma& lemma) const override;
    bool insertIfNew(const TheoryLemma& lemma) override;
    bool isInstalled(const TheoryLemma& lemma) const override;
    void markInstalled(const TheoryLemma& lemma) override;

private:
    std::unordered_set<uint64_t> emitted_;
    std::unordered_set<uint64_t> installed_;
    // FIFO order for eviction. Invariant (insert/evict move in lockstep):
    // |fifo| == |set|, the fifo lists present keys in insertion order, so each
    // key appears at most once.
    std::deque<uint64_t> emittedFifo_;
    std::deque<uint64_t> installedFifo_;

    bool mgmtChecked_ = false;
    size_t cap_ = 0;  // 0 == unbounded (flag OFF)
    void ensureMgmt();
    void evictIfNeeded(std::unordered_set<uint64_t>& set, std::deque<uint64_t>& fifo);

    static uint64_t computeKey(const TheoryLemma& lemma);
};

} // namespace zolver
