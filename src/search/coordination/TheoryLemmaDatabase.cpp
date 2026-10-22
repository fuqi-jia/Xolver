#include "base/RuntimeConfig.h"
#include "base/EnvParam.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <algorithm>
#include <cstdlib>

namespace xolver {

void TheoryLemmaDatabase::ensureMgmt() {
    if (mgmtChecked_) return;
    mgmtChecked_ = true;
    cap_ = static_cast<size_t>(xolver::config::read<xolver::config::ReadKind::Capacity>("XOLVER_SAT_LEMMA_MGMT"));
}

void TheoryLemmaDatabase::evictIfNeeded(KeySet& set, std::deque<Key>& fifo) {
    if (cap_ == 0) return;
    while (set.size() > cap_ && !fifo.empty()) {
        set.erase(fifo.front());
        fifo.pop_front();
    }
}

size_t TheoryLemmaDatabase::KeyHash::operator()(const Key& clause) const {
    uint64_t key = 0x9e3779b97f4a7c15ULL;
    for (auto literal : clause)
        key ^= literal + 0x9e3779b97f4a7c15ULL + (key << 6) + (key >> 2);
    return key;
}

TheoryLemmaDatabase::Key TheoryLemmaDatabase::computeKey(const TheoryLemma& lemma) {
    Key key;
    key.reserve(lemma.lits.size());
    for (auto lit : lemma.lits)
        key.push_back((static_cast<uint64_t>(lit.var) << 1) | (lit.sign ? 1 : 0));
    std::sort(key.begin(), key.end());
    key.erase(std::unique(key.begin(), key.end()), key.end());
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

} // namespace xolver
