#include "search/bitblast/IntegerRadixEncoder.h"
#include "search/bitblast/SpaceEstimator.h"
#include <algorithm>
#include <numeric>
#include <unordered_set>

namespace xolver::bitblast {

std::vector<size_t> encodeIntegerRadixDefinitions(
    BitBlastEncoder& encoder, const std::vector<IntegerRadixDecomposition>& definitions,
    std::unordered_map<std::string, BitVec>& values, const IntegerBoundsLookup& bounds,
    WorkBudget& budget, std::chrono::steady_clock::time_point deadline) {
    auto tick = [&] {
        budget.tick();
        if ((budget.used() & 1023) == 0 && std::chrono::steady_clock::now() >= deadline)
            throw ResourceExhausted("integer radix encoding budget exhausted");
    };
    auto require = [&](SatLit literal) {
        tick();
        if (literal != encoder.constTrue()) encoder.assertLit(literal);
    };
    auto fit = [&](BitVec value, const std::pair<mpz_class, mpz_class>& range) {
        const unsigned width = SpaceEstimator::bitsToCover(range.first, range.second);
        const auto sign = value.sign();
        while (value.width() < width) { tick(); value.bits.push_back(sign); }
        const auto retainedSign = value.bits[width - 1];
        for (size_t bit = width; bit < value.bits.size(); ++bit)
            require(encoder.xorGate(value.bits[bit], retainedSign).negated());
        value.bits.resize(width);
        if (range.first >= 0) {
            require(value.bits.back().negated());
            value.bits.back() = encoder.constFalse();
        } else if (range.second < 0) {
            require(value.bits.back());
            value.bits.back() = encoder.constTrue();
        }
        value.isConst = false;
        return value;
    };
    std::vector<size_t> order(definitions.size());
    std::iota(order.begin(), order.end(), 0);
    std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
        const auto x = values.find(definitions[a].dividend), y = values.find(definitions[b].dividend);
        return (x == values.end() ? 0 : x->second.width()) < (y == values.end() ? 0 : y->second.width());
    });
    std::unordered_set<std::string> read, assigned;
    std::vector<size_t> applied;
    for (size_t index : order) {
        tick();
        const auto& definition = definitions[index];
        if (read.contains(definition.dividend) || assigned.contains(definition.dividend)) continue;
        const auto x = values.find(definition.dividend), q = values.find(definition.quotient),
                   r = values.find(definition.remainder);
        if (x == values.end() || q == values.end() || r == values.end() ||
            x->second.bits.empty() || q->second.bits.empty() || r->second.bits.empty()) continue;
        const mpz_class radix = mpz_class(1) << definition.exponent;
        if (definition.remainderLower < 0 || definition.remainderUpper < definition.remainderLower ||
            definition.remainderUpper >= radix) continue;
        // These clauses preserve the remainder's numerical value while making
        // its nonnegative, at-most-exponent-bit representation explicit.
        auto remainder = fit(r->second, {definition.remainderLower, definition.remainderUpper});
        auto quotient = definition.negateQuotient ? encoder.neg(q->second) : q->second;
        if (encoder.overflowed()) break;
        BitVec value;
        const auto high = remainder.sign();
        for (unsigned bit = 0; bit < definition.exponent; ++bit) {
            tick();
            value.bits.push_back(bit < remainder.width() ? remainder.bits[bit] : high);
        }
        value.bits.insert(value.bits.end(), quotient.bits.begin(), quotient.bits.end());
        if (definition.offset != 0) value = encoder.sub(value, encoder.mkConst(definition.offset));
        if (encoder.overflowed()) break;
        if (const auto range = bounds(definition.dividend)) {
            if (range->first > range->second) continue;
            value = fit(std::move(value), *range);
        }
        if (encoder.overflowed()) break;
        x->second = std::move(value);
        read.insert(definition.quotient);
        read.insert(definition.remainder);
        assigned.insert(definition.dividend);
        applied.push_back(index);
    }
    return applied;
}

} // namespace xolver::bitblast
