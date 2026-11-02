#include "search/bitblast/PseudoBooleanEncoder.h"
#include <algorithm>
#include <map>
#include <limits>

namespace xolver::bitblast {

bool PseudoBooleanEncoder::SumLess::operator()(
    const std::vector<WeightedLiteral>& left, const std::vector<WeightedLiteral>& right) const {
    if (left.size() != right.size()) return left.size() < right.size();
    for (size_t i = 0; i < left.size(); ++i) {
        if (left[i].literal.var != right[i].literal.var)
            return left[i].literal.var < right[i].literal.var;
        if (left[i].literal.sign != right[i].literal.sign)
            return left[i].literal.sign < right[i].literal.sign;
        if (left[i].weight != right[i].weight) return left[i].weight < right[i].weight;
    }
    return false;
}

void PseudoBooleanEncoder::tick() {
    work_.tick();
    if (encoder_.overflowed() || ((work_.used() & 1023) == 0 &&
        std::chrono::steady_clock::now() >= deadline_))
        throw ResourceExhausted("pseudo-Boolean encoding budget exhausted");
}

bool PseudoBooleanEncoder::diagramFitsBudget(
    const std::vector<WeightedLiteral>& terms, const std::vector<mpz_class>& suffix,
    const mpz_class& bound) {
    if (!encoder_.remainingVarBudget() && !work_.remaining()) return false;
    // A global allocation limit says little about whether one threshold is
    // affordable: a single exponential diagram can consume the whole arm's
    // wall time before any SAT search. Extend a diagram beyond the arithmetic
    // cost only when its complete state bound is quadratic in its inputs.
    // This selects an encoding; exceeding it still uses the exact shared sum.
    const mpz_class inputs = terms.size();
    const mpz_class structuralLimit = inputs * inputs;
    auto capacity = [&] {
        uint64_t result = encoder_.remainingVarBudget().value_or(std::numeric_limits<uint64_t>::max());
        if (const auto work = work_.remaining()) {
            // A complete memoized diagram with N expanded states performs
            // at most 4N+1 loop iterations, each charging one work unit.
            result = std::min<uint64_t>(result, *work ? (*work - 1)/4 : 0);
        }
        return result;
    };
    mpz_class prefixWeight = 0, prefixGcd = 0, assignments = 1, states = 0;
    for (size_t index = 0; index < terms.size(); ++index) {
        tick();
        // Residual b is bound minus a prefix sum. Such sums lie between zero
        // and prefixWeight and are multiples of prefixGcd. Only residuals in
        // [0,suffix[index]-1] can create nonconstant diagram nodes.
        const mpz_class lower = std::max(mpz_class(0), mpz_class(bound - prefixWeight));
        const mpz_class upper = std::min(bound, mpz_class(suffix[index] - 1));
        if (lower <= upper) {
            const mpz_class residues = prefixGcd == 0 ? mpz_class(1)
                : mpz_class((upper - lower)/prefixGcd + 1);
            states += std::min(assignments, residues);
            // iteGate creates at most one SAT variable per expanded state.
            // Using remaining resources after the partial diagram and this
            // estimate is conservative: it reserves the full diagram again.
            if (states > structuralLimit || states > capacity()) return false;
        }
        prefixWeight += terms[index].weight;
        mpz_gcd(prefixGcd.get_mpz_t(), prefixGcd.get_mpz_t(), terms[index].weight.get_mpz_t());
        assignments <<= 1;
    }
    return states <= capacity();
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
        if (bound >= suffix[0]) return encoder_.constTrue();
        // S <= b is equivalent to !(T-S <= T-b-1), where T is the
        // total positive weight. A single polarity convention lets opposite
        // inequalities and different bounds share the same arithmetic sum.
        const bool complement = !terms.front().literal.sign;
        if (complement) {
            bound = suffix[0] - bound - 1;
            for (auto& term : terms) term.literal = term.literal.negated();
        }
        auto oriented = [&](std::optional<SatLit> literal) {
            if (literal && complement) *literal = literal->negated();
            return literal;
        };
        // Once a sum needed an arithmetic encoding, subsequent thresholds
        // reuse it before trying another potentially large decision diagram.
        if (const auto found = sums_.find(terms); found != sums_.end()) {
            ++statistics_.carrySaveThresholds;
            ++statistics_.reusedSums;
            return oriented(compareSum(found->second, bound));
        }
        // Several individually affordable diagrams can still duplicate most
        // of the encoding for a family of bounds. Once this sum needed a large
        // complete diagram, a new threshold makes the shared arithmetic
        // representation useful. Existing diagram literals remain exact.
        if (diagramSums_.contains(terms))
            return oriented(carrySaveThreshold(terms, bound));

        // A full adder needs at most five gates; the final addition/comparison
        // is linear in the coefficient width. If a diagram exceeds that
        // structural estimate, check whether its full state space fits the
        // existing budgets before sacrificing its stronger propagation.
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
        bool keepDiagram = false;
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
                if (++expanded > circuitCost && !keepDiagram) {
                    // A smaller adder need not propagate as strongly as the
                    // diagram. Keep the diagram when its whole state space
                    // provably fits the existing variable and work limits.
                    keepDiagram = diagramFitsBudget(terms, suffix, target);
                    if (keepDiagram) ++statistics_.diagramBudgetProofs;
                }
                if (expanded > circuitCost && !keepDiagram) {
                    // Every emitted gate is only a total-function definition;
                    // no source predicate has been asserted. Discarding the
                    // partial diagram therefore cannot restrict the inputs.
                    stack.clear();
                    memo.clear();
                    return oriented(carrySaveThreshold(terms, target));
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
        if (keepDiagram) diagramSums_.insert(std::move(terms));
        return oriented(result);
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
    // Publish only a complete sum. Partial gates from exhausted attempts
    // never become a reusable expression or an exposed threshold predicate.
    sums_.emplace(terms, sum);
    ++statistics_.carrySaveSums;
    return compareSum(sum, bound);
}

std::optional<SatLit> PseudoBooleanEncoder::compareSum(
    const BitVec& sum, const mpz_class& bound) {
    const auto difference = encoder_.sub(sum, encoder_.mkConst(bound));
    if (encoder_.overflowed()) return std::nullopt;
    const auto predicate = encoder_.relZero(difference, Relation::Leq);
    if (encoder_.overflowed()) return std::nullopt;
    return predicate;
}

} // namespace xolver::bitblast
