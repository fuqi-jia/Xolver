#pragma once

#include "base/WorkBudget.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <chrono>
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
// are normalized before building a shared decision diagram. No recursion is
// used. Exhaustion returns no literal; a partial encoding must not be asserted.
class PseudoBooleanEncoder {
public:
    PseudoBooleanEncoder(BitBlastEncoder& encoder, WorkBudget& work,
        std::chrono::steady_clock::time_point deadline =
            std::chrono::steady_clock::time_point::max())
        : encoder_(encoder), work_(work), deadline_(deadline) {}

    std::optional<SatLit> lessEqual(std::vector<WeightedLiteral> terms, mpz_class bound);

private:
    BitBlastEncoder& encoder_;
    WorkBudget& work_;
    std::chrono::steady_clock::time_point deadline_;
    void tick();
};

} // namespace xolver::bitblast
