#include "search/bitblast/PseudoBooleanEncoder.h"
#include <algorithm>
#include <map>
#include <limits>

namespace xolver::bitblast {

void PseudoBooleanEncoder::tick() {
    work_.tick();
    if (encoder_.overflowed() || ((work_.used() & 1023) == 0 &&
        std::chrono::steady_clock::now() >= deadline_))
        throw ResourceExhausted("pseudo-Boolean encoding budget exhausted");
}

std::optional<SatLit> PseudoBooleanEncoder::lessEqual(
    std::vector<WeightedLiteral> terms, mpz_class bound) {
    ++statistics_.thresholds;
    try {
        // w*[not x] + v*[x] = min(w,v) + |w-v|*[heavier polarity].
        std::map<SatVar, std::pair<mpz_class, mpz_class>> coefficients;
        for (auto& term : terms) {
            tick();
            if (term.literal.var == 0) return std::nullopt;
            if (term.weight < 0) {
                bound -= term.weight;
                term.weight = -term.weight;
                term.literal = term.literal.negated();
            }
            if (term.literal == encoder_.constTrue()) bound -= term.weight;
            else if (term.literal != encoder_.constFalse()) {
                auto& pair = coefficients[term.literal.var];
                (term.literal.sign ? pair.first : pair.second) += term.weight;
            }
        }
        terms.clear();
        mpz_class gcd = 0;
        for (const auto& [variable, pair] : coefficients) {
            tick();
            bound -= std::min(pair.first, pair.second);
            mpz_class difference = pair.first - pair.second;
            if (difference == 0) continue;
            const bool positive = difference > 0;
            if (!positive) difference = -difference;
            mpz_gcd(gcd.get_mpz_t(), gcd.get_mpz_t(), difference.get_mpz_t());
            terms.push_back({SatLit(variable, positive), std::move(difference)});
        }
        if (bound < 0) return encoder_.constFalse();
        if (terms.empty()) return encoder_.constTrue();
        if (gcd > 1) {
            mpz_fdiv_q(bound.get_mpz_t(), bound.get_mpz_t(), gcd.get_mpz_t());
            for (auto& term : terms) term.weight /= gcd;
        }
        std::sort(terms.begin(), terms.end(), [](const auto& a, const auto& b) {
            return a.weight != b.weight ? a.weight > b.weight : a.literal.var < b.literal.var;
        });
        std::vector<mpz_class> suffix(terms.size() + 1);
        for (size_t i = terms.size(); i-- > 0;) suffix[i] = suffix[i + 1] + terms[i].weight;

        // A full adder needs at most five gates; the final addition/comparison
        // is linear in the coefficient width. Prefer a diagram while its
        // observed state count is cheaper than that structural alternative.
        size_t circuitCost = 0, maximumWidth = 0;
        const auto maximum = std::numeric_limits<size_t>::max();
        auto charge = [&](size_t amount, size_t multiplier) {
            circuitCost = amount > (maximum - circuitCost) / multiplier
                ? maximum : circuitCost + amount * multiplier;
        };
        for (const auto& term : terms) {
            tick();
            charge(mpz_popcount(term.weight.get_mpz_t()), 5);
            maximumWidth = std::max(maximumWidth, mpz_sizeinbase(term.weight.get_mpz_t(), 2));
        }
        charge(maximumWidth, 16);
        const mpz_class target = bound;

        // F(i,b) = ite(literal_i, F(i+1,b-weight_i), F(i+1,b)).
        // Memoization is local to this normalized threshold. Gate sharing in
        // BitBlastEncoder also shares equivalent subexpressions across atoms.
        std::vector<std::map<mpz_class, SatLit>> memo(terms.size());
        struct Frame {
            size_t index;
            mpz_class bound;
            unsigned phase = 0;
            SatLit low;
        };
        std::vector<Frame> stack;
        stack.push_back({0, std::move(bound), 0, {}});
        SatLit result = encoder_.constFalse();
        size_t expanded = 0;
        while (!stack.empty()) {
            tick();
            auto& frame = stack.back();
            const size_t index = frame.index;
            if (frame.phase == 0) {
                if (frame.bound < 0 || frame.bound >= suffix[index]) {
                    result = frame.bound < 0 ? encoder_.constFalse() : encoder_.constTrue();
                    stack.pop_back();
                    continue;
                }
                const auto cached = memo[index].find(frame.bound);
                if (cached != memo[index].end()) {
                    result = cached->second;
                    stack.pop_back();
                    continue;
                }
                ++statistics_.diagramStates;
                if (++expanded > circuitCost) {
                    // Every emitted gate is only a total-function definition;
                    // no source predicate has been asserted. Discarding the
                    // partial diagram therefore cannot restrict the inputs.
                    stack.clear();
                    memo.clear();
                    return carrySaveThreshold(terms, target);
                }
                frame.phase = 1;
                const mpz_class lowBound = frame.bound;
                stack.push_back({index + 1, lowBound, 0, {}});
            } else if (frame.phase == 1) {
                frame.low = result;
                frame.phase = 2;
                const mpz_class highBound = frame.bound - terms[index].weight;
                stack.push_back({index + 1, highBound, 0, {}});
            } else {
                result = encoder_.iteGate(terms[index].literal, result, frame.low);
                if (encoder_.overflowed()) return std::nullopt;
                memo[index].emplace(frame.bound, result);
                stack.pop_back();
            }
        }
        return result;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

std::optional<SatLit> PseudoBooleanEncoder::carrySaveThreshold(
    const std::vector<WeightedLiteral>& terms, const mpz_class& bound) {
    ++statistics_.carrySaveThresholds;
    std::vector<std::vector<SatLit>> columns;
    for (const auto& term : terms) {
        const size_t width = mpz_sizeinbase(term.weight.get_mpz_t(), 2);
        if (columns.size() < width) columns.resize(width);
        for (size_t bit = 0; bit < width; ++bit) {
            tick();
            if (mpz_tstbit(term.weight.get_mpz_t(), bit)) columns[bit].push_back(term.literal);
        }
    }
    for (size_t bit = 0; bit < columns.size(); ++bit) {
        while (columns[bit].size() >= 3) {
            tick();
            const auto a = columns[bit].back(); columns[bit].pop_back();
            const auto b = columns[bit].back(); columns[bit].pop_back();
            const auto c = columns[bit].back(); columns[bit].pop_back();
            const auto axb = encoder_.xorGate(a, b);
            const auto sum = encoder_.xorGate(axb, c);
            const auto ab = encoder_.andGate(a, b);
            const auto ac = encoder_.andGate(axb, c);
            const auto carry = encoder_.orGate(ab, ac);
            if (encoder_.overflowed()) return std::nullopt;
            ++statistics_.compressors;
            if (sum != encoder_.constFalse()) columns[bit].push_back(sum);
            if (carry != encoder_.constFalse()) {
                if (columns.size() <= bit + 1) columns.resize(bit + 2);
                columns[bit + 1].push_back(carry);
            }
        }
    }
    // Each operand has an explicit zero sign bit. Width-growing addition and
    // subtraction preserve the complete unsigned sum as a signed integer;
    // neither a carry nor an arbitrary-size bound is truncated.
    BitVec left, right;
    left.bits.assign(columns.size() + 1, encoder_.constFalse());
    right.bits = left.bits;
    for (size_t bit = 0; bit < columns.size(); ++bit) {
        tick();
        if (!columns[bit].empty()) left.bits[bit] = columns[bit][0];
        if (columns[bit].size() == 2) right.bits[bit] = columns[bit][1];
    }
    const auto sum = encoder_.add(left, right);
    if (encoder_.overflowed()) return std::nullopt;
    const auto difference = encoder_.sub(sum, encoder_.mkConst(bound));
    if (encoder_.overflowed()) return std::nullopt;
    const auto predicate = encoder_.relZero(difference, Relation::Leq);
    if (encoder_.overflowed()) return std::nullopt;
    return predicate;
}

} // namespace xolver::bitblast
