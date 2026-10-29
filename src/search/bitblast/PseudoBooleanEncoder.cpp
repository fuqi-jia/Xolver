#include "search/bitblast/PseudoBooleanEncoder.h"
#include <algorithm>
#include <map>

namespace xolver::bitblast {

void PseudoBooleanEncoder::tick() {
    work_.tick();
    if (encoder_.overflowed() || ((work_.used() & 1023) == 0 &&
        std::chrono::steady_clock::now() >= deadline_))
        throw ResourceExhausted("pseudo-Boolean encoding budget exhausted");
}

std::optional<SatLit> PseudoBooleanEncoder::lessEqual(
    std::vector<WeightedLiteral> terms, mpz_class bound) {
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

} // namespace xolver::bitblast
