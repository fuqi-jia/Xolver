#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <unordered_set>

namespace nlcolver {

class TheoryLemmaDatabase : public TheoryLemmaStorage {
public:
    bool contains(const TheoryLemma& lemma) const override;
    bool insertIfNew(const TheoryLemma& lemma) override;
    bool isInstalled(const TheoryLemma& lemma) const override;
    void markInstalled(const TheoryLemma& lemma) override;

private:
    std::unordered_set<uint64_t> emitted_;
    std::unordered_set<uint64_t> installed_;
    static uint64_t computeKey(const TheoryLemma& lemma);
};

} // namespace nlcolver
