#include "theory/core/TheoryLemmaDatabase.h"
#include <algorithm>
#include <cstdlib>

namespace zolver {

void TheoryLemmaDatabase::ensureMgmt() {
    if (mgmtChecked_) return;
    mgmtChecked_ = true;
    const char* env = std::getenv("ZOLVER_SAT_LEMMA_MGMT");
    if (!env) { cap_ = 0; return; }  // unbounded (flag OFF)
    long v = std::atol(env);
    cap_ = (v > 0) ? static_cast<size_t>(v) : 100000;  // bare flag => default cap
}

void TheoryLemmaDatabase::evictIfNeeded(std::unordered_set<uint64_t>& set,
                                        std::deque<uint64_t>& fifo) {
    if (cap_ == 0) return;
    while (set.size() > cap_ && !fifo.empty()) {
        uint64_t oldest = fifo.front();
        fifo.pop_front();
        set.erase(oldest);  // front is the oldest present key (invariant)
    }
}

uint64_t TheoryLemmaDatabase::computeKey(const TheoryLemma& lemma) {
    uint64_t key = 0x9e3779b97f4a7c15ULL;
    auto sorted = lemma.lits;
    std::sort(sorted.begin(), sorted.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    for (auto lit : sorted) {
        key ^= static_cast<uint64_t>(lit.var) + 0x9e3779b97f4a7c15ULL + (key << 6) + (key >> 2);
        key ^= static_cast<uint64_t>(lit.sign ? 1 : 0) + 0x9e3779b97f4a7c15ULL + (key << 6) + (key >> 2);
    }
    return key;
}

bool TheoryLemmaDatabase::contains(const TheoryLemma& lemma) const {
    return emitted_.count(computeKey(lemma)) != 0;
}

bool TheoryLemmaDatabase::insertIfNew(const TheoryLemma& lemma) {
    ensureMgmt();
    bool inserted = emitted_.insert(computeKey(lemma)).second;
    if (inserted && cap_ != 0) {
        emittedFifo_.push_back(computeKey(lemma));
        evictIfNeeded(emitted_, emittedFifo_);
    }
    return inserted;
}

bool TheoryLemmaDatabase::isInstalled(const TheoryLemma& lemma) const {
    return installed_.count(computeKey(lemma)) != 0;
}

void TheoryLemmaDatabase::markInstalled(const TheoryLemma& lemma) {
    ensureMgmt();
    bool inserted = installed_.insert(computeKey(lemma)).second;
    if (inserted && cap_ != 0) {
        installedFifo_.push_back(computeKey(lemma));
        evictIfNeeded(installed_, installedFifo_);
    }
}

} // namespace zolver
