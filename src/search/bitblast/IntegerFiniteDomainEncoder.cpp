#include "search/bitblast/IntegerFiniteDomainEncoder.h"
#include "search/bitblast/SpaceEstimator.h"
#include <algorithm>

namespace xolver::bitblast {

std::optional<EncodedIntegerDomain> encodeIntegerFiniteDomain(
    BitBlastEncoder& encoder, std::vector<mpz_class> points, WorkBudget& budget,
    std::chrono::steady_clock::time_point deadline) {
    auto tick = [&] {
        budget.tick();
        if (encoder.overflowed() || std::chrono::steady_clock::now() >= deadline)
            throw ResourceExhausted("finite integer domain encoding exhausted");
    };
    try {
        tick();
        std::sort(points.begin(), points.end());
        points.erase(std::unique(points.begin(), points.end()), points.end());
        if (points.empty()) return std::nullopt;
        EncodedIntegerDomain result;
        const unsigned width = SpaceEstimator::bitsToCover(points.front(), points.back());
        if (points.size() == 1) {
            result.value = encoder.mkConst(points.front(), width);
            result.choices.emplace_back(points.front(), encoder.constTrue());
            return result;
        }
        auto seen = encoder.constFalse();
        for (const auto& point : points) {
            tick();
            const auto selector = encoder.mkVar(1).bits[0];
            // A linear-size prefix enforces at most one selected point.
            encoder.assertLit(encoder.andGate(seen, selector).negated());
            seen = encoder.orGate(seen, selector);
            result.choices.emplace_back(point, selector);
        }
        encoder.assertLit(seen);
        result.value.bits.assign(width, encoder.constFalse());
        for (const auto& [point, selector] : result.choices) {
            for (unsigned bit = 0; bit < width; ++bit) {
                tick();
                // GMP tests negative values using two's-complement semantics.
                if (mpz_tstbit(point.get_mpz_t(), bit))
                    result.value.bits[bit] = encoder.orGate(result.value.bits[bit], selector);
            }
        }
        tick();
        return result;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

} // namespace xolver::bitblast
