#include "theory/core/TheoryLemmaDatabase.h"
#include <algorithm>

namespace nlcolver {

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
    return emitted_.insert(computeKey(lemma)).second;
}

} // namespace nlcolver
