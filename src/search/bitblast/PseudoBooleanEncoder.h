#pragma once

#include "base/WorkBudget.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <chrono>
#include <cstddef>
#include <optional>
#include <vector>

namespace xolver::bitblast {

struct WeightedLiteral {
    SatLit literal;
    mpz_class weight;
};

// Fully reified exact integer threshold: the returned literal is equivalent to
// sum(weight * [literal]) <= bound, including under negation or disjunction.
// Signed weights, repeated/complementary literals and arbitrary-size integers
// are normalized before building a shared decision diagram. If its state
// count exceeds the estimated arithmetic-circuit size, an exact carry-save
// sum replaces the diagram. Exhaustion exposes no unfinished literal.
class PseudoBooleanEncoder {
public:
    struct Statistics {
        size_t thresholds = 0;
        size_t diagramStates = 0;
        size_t carrySaveThresholds = 0;
        size_t compressors = 0;
    };
    PseudoBooleanEncoder(BitBlastEncoder& encoder, WorkBudget& work,
        std::chrono::steady_clock::time_point deadline =
            std::chrono::steady_clock::time_point::max())
        : encoder_(encoder), work_(work), deadline_(deadline) {}

    std::optional<SatLit> lessEqual(std::vector<WeightedLiteral> terms, mpz_class bound);
    const Statistics& statistics() const { return statistics_; }

private:
    BitBlastEncoder& encoder_;
    WorkBudget& work_;
    std::chrono::steady_clock::time_point deadline_;
    Statistics statistics_;
    void tick();
    std::optional<SatLit> carrySaveThreshold(
        const std::vector<WeightedLiteral>& terms, const mpz_class& bound);
};

} // namespace xolver::bitblast
