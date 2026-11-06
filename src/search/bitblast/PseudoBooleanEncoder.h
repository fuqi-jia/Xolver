#pragma once

#include "base/WorkBudget.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <chrono>
#include <cstddef>
#include <map>
#include <optional>
#include <set>
#include <vector>

namespace xolver::bitblast {

struct WeightedLiteral {
    SatLit literal;
    mpz_class weight;
};

// Fully reified exact integer threshold: the returned literal is equivalent to
// sum(weight * [literal]) <= bound, including under negation or disjunction.
// Signed weights, repeated/complementary literals and arbitrary-size integers
// are normalized before building a shared decision diagram. Complete diagrams
// are retained when their state space provably fits the declared budgets.
// An expensive diagram is attempted once per normalized sum; further bounds
// use a shared arithmetic sum to amortize their encoding instead.
// Otherwise an exact carry-save sum can replace an expanding diagram and be
// reused across bounds and complemented inequalities. Exhaustion exposes no
// unfinished literal.
class PseudoBooleanEncoder {
public:
    struct Statistics {
        size_t thresholds = 0;
        size_t diagramStates = 0;
        size_t diagramBudgetProofs = 0;
        size_t carrySaveThresholds = 0;
        size_t carrySaveSums = 0;
        size_t reusedSums = 0;
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
    struct SumLess {
        bool operator()(const std::vector<WeightedLiteral>& left,
                        const std::vector<WeightedLiteral>& right) const;
    };
    // Complete exact sums in this encoder's SAT instance. Bounds and
    // threshold polarities are deliberately absent from the expression key.
    std::map<std::vector<WeightedLiteral>, BitVec, SumLess> sums_;
    // Only completed diagrams that exceeded the arithmetic cost are recorded.
    // A later threshold over the same sum can amortize an arithmetic encoding;
    // an isolated threshold retains the diagram's stronger propagation.
    std::set<std::vector<WeightedLiteral>, SumLess> diagramSums_;
    void tick();
    bool diagramFitsBudget(const std::vector<WeightedLiteral>& terms,
                           const std::vector<mpz_class>& suffix, const mpz_class& bound);
    std::optional<SatLit> compareSum(const BitVec& sum, const mpz_class& bound);
    std::optional<SatLit> carrySaveThreshold(
        const std::vector<WeightedLiteral>& terms, const mpz_class& bound);
};

} // namespace xolver::bitblast
