#pragma once

#include "theory/core/TheorySolver.h"
#include <unordered_set>

namespace nlcolver {

class TheoryLemmaDatabase {
public:
    bool contains(const TheoryLemma& lemma) const;
    bool insertIfNew(const TheoryLemma& lemma);

private:
    std::unordered_set<uint64_t> emitted_;
    static uint64_t computeKey(const TheoryLemma& lemma);
};

} // namespace nlcolver
