#pragma once

#include "sat/SatSolver.h"
#include <vector>
#include <cstdint>
#include <algorithm>

namespace nlcolver {

/**
 * O(1) duplicate/opposite-polarity detection for active theory literals.
 *
 * Uses per-polarity epoch stamps.  Backtrack must rebuild the set from
 * the current active container (e.g. after resize).
 */
class ActiveLiteralSet {
public:
    enum class InsertResult {
        Inserted,
        Duplicate,
        OppositePolarity
    };

    ActiveLiteralSet() = default;

    /**
     * Try to insert a literal.
     *
     * @return InsertResult::Inserted          if new
     *         InsertResult::Duplicate         if same (var,sign) already present
     *         InsertResult::OppositePolarity  if complementary literal present
     */
    InsertResult insert(SatLit lit) {
        ensureSize(lit.var);

        auto& same = lit.sign ? posSeen_ : negSeen_;
        auto& opp  = lit.sign ? negSeen_ : posSeen_;

        if (opp[lit.var] == currentEpoch_) {
            return InsertResult::OppositePolarity;
        }

        if (same[lit.var] == currentEpoch_) {
            return InsertResult::Duplicate;
        }

        same[lit.var] = currentEpoch_;
        return InsertResult::Inserted;
    }

    bool contains(SatLit lit) const {
        if (lit.var >= posSeen_.size()) return false;
        auto& same = lit.sign ? posSeen_ : negSeen_;
        return same[lit.var] == currentEpoch_;
    }

    /** Increment epoch (cheap O(1) reset). */
    void newEpoch() {
        ++currentEpoch_;
        if (currentEpoch_ == 0) {
            // Epoch overflow: extremely unlikely, but handle gracefully.
            currentEpoch_ = 1;
            std::fill(posSeen_.begin(), posSeen_.end(), 0);
            std::fill(negSeen_.begin(), negSeen_.end(), 0);
        }
    }

    /** Full reset: equivalent to newEpoch(). */
    void reset() { newEpoch(); }

    /**
     * Rebuild the seen-set from an active container.
     * Call this after backtrack-resize to restore consistency.
     */
    template <typename Container, typename GetLit>
    void rebuildFromActive(const Container& active, GetLit getLit) {
        newEpoch();
        for (const auto& item : active) {
            // We assume active contains no opposite-polarity pairs;
            // they were filtered at insert time.
            insert(getLit(item));
        }
    }

private:
    uint32_t currentEpoch_ = 1;
    std::vector<uint32_t> posSeen_;
    std::vector<uint32_t> negSeen_;

    void ensureSize(SatVar var) {
        if (var >= posSeen_.size()) {
            posSeen_.resize(static_cast<size_t>(var) + 1, 0);
            negSeen_.resize(static_cast<size_t>(var) + 1, 0);
        }
    }
};

} // namespace nlcolver
