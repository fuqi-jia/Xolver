#include "base/RuntimeConfig.h"
#include "search/bitblast/PolyBitBlaster.h"
#include "base/EnvParam.h"
#include <algorithm>
#include <cstdlib>
#include <iostream>

namespace xolver::bitblast {

PolyBitBlaster::PolyBitBlaster(BitBlastEncoder& enc, PolynomialKernel& kernel,
                               const std::unordered_map<std::string, BitVec>& varBits)
    : enc_(enc), kernel_(kernel), varBits_(varBits) {}

BitVec PolyBitBlaster::encodeMonomial(const PolynomialKernel::MonomialTerm& m) {
    if (m.powers.empty()) return enc_.mkConst(m.coefficient);

    // Canonical VarId order so monomials sharing leading factors share encoded
    // sub-products (CSE). Build the product one factor at a time, caching every
    // prefix keyed by its (VarId, cumulative-exp) list.
    std::vector<std::pair<VarId, int>> sorted(m.powers.begin(), m.powers.end());
    std::sort(sorted.begin(), sorted.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    std::vector<std::pair<VarId, int>> prefix;   // cache key built incrementally
    BitVec prod;
    bool first = true;
    for (const auto& pe : sorted) {
        const BitVec& vb = varBits_.at(std::string(kernel_.varName(pe.first)));
        for (int k = 0; k < pe.second; ++k) {
            // extend prefix by one occurrence of this variable
            if (!prefix.empty() && prefix.back().first == pe.first) prefix.back().second += 1;
            else prefix.emplace_back(pe.first, 1);

            auto it = productCache_.find(prefix);
            if (it != productCache_.end()) {
                prod = it->second;                  // reuse the already-encoded sub-product
            } else {
                prod = first ? vb : enc_.mul(prod, vb);
                productCache_.emplace(prefix, prod);
            }
            first = false;
        }
    }
    // Skip the mul-by-one to avoid unnecessary width growth.
    if (m.coefficient == 1) return prod;
    // Coefficient-times-product cache. Repeated `(* k S_i)` across atoms
    // (e.g. mcm/113's 442+493 disjunct alternatives) share the same mulConst
    // shift-add chain. Key on (coefficient string, sorted prefix). Sound:
    // mulConst is a pure function of its inputs and the encoder's current
    // wiring. Lives for ONE solve() iteration like productCache_.
    auto cmKey = std::make_pair(m.coefficient.get_str(), sorted);
    auto cmIt = coeffMonomialCache_.find(cmKey);
    if (cmIt != coeffMonomialCache_.end()) return cmIt->second;
    BitVec coeffProd = enc_.mulConst(m.coefficient, prod);
    coeffMonomialCache_.emplace(std::move(cmKey), coeffProd);
    return coeffProd;
}

BitVec PolyBitBlaster::encodePoly(PolyId p) {
    auto termsOpt = kernel_.terms(p);
    if (!termsOpt || termsOpt->empty()) return enc_.mkConst(mpz_class(0), 1);
    return encodeSum(*termsOpt);
}

BitVec PolyBitBlaster::encodeSum(const std::vector<PolynomialKernel::MonomialTerm>& terms) {
    std::vector<BitVec> monos;
    monos.reserve(terms.size());
    for (const auto& m : terms) monos.push_back(encodeMonomial(m));

    // Greedy Addition: repeatedly fold the two narrowest summands.
    while (monos.size() > 1) {
        std::sort(monos.begin(), monos.end(),
                  [](const BitVec& a, const BitVec& b) { return a.width() < b.width(); });
        BitVec s = enc_.add(monos[0], monos[1]);
        monos.erase(monos.begin(), monos.begin() + 2);
        monos.push_back(s);
    }
    return monos.front();
}

SatLit PolyBitBlaster::encodeConstraint(const NormalizedNiaConstraint& c) {
    auto terms = kernel_.terms(c.poly);
    if (terms && !terms->empty()) {
        // p = m*q: comparing p with zero needs the factors' zero/sign bits,
        // not the magnitude of their product. Retain m=0 explicitly: cancelling
        // a possibly-zero factor would change both equalities and inequalities.
        std::map<VarId, int> common(terms->front().powers.begin(), terms->front().powers.end());
        for (size_t i = 1; i < terms->size() && !common.empty(); ++i) {
            for (auto it = common.begin(); it != common.end();) {
                const auto& powers = (*terms)[i].powers;
                const auto power = std::find_if(powers.begin(), powers.end(),
                    [&](const auto& entry) { return entry.first == it->first; });
                if (power == powers.end()) it = common.erase(it);
                else { it->second = std::min(it->second, power->second); ++it; }
            }
        }
        if (!common.empty()) {
            SatLit factorZero = enc_.constFalse();
            SatLit factorNegative = enc_.constFalse();
            for (const auto& [variable, exponent] : common) {
                const auto& bits = varBits_.at(std::string(kernel_.varName(variable)));
                factorZero = enc_.orGate(factorZero, enc_.isZero(bits));
                if (exponent % 2 != 0)
                    factorNegative = enc_.xorGate(factorNegative, bits.sign());
            }
            for (auto& term : *terms) {
                for (auto& [variable, exponent] : term.powers) {
                    const auto found = common.find(variable);
                    if (found != common.end()) exponent -= found->second;
                }
                std::erase_if(term.powers, [](const auto& power) { return power.second == 0; });
            }
            const auto quotient = encodeSum(*terms);
            const auto zero = enc_.orGate(factorZero, enc_.isZero(quotient));
            const auto negative = enc_.andGate(zero.negated(),
                enc_.xorGate(factorNegative, quotient.sign()));
            switch (c.rel) {
                case Relation::Eq: return zero;
                case Relation::Neq: return zero.negated();
                case Relation::Lt: return negative;
                case Relation::Geq: return negative.negated();
                case Relation::Leq: return enc_.orGate(zero, negative);
                case Relation::Gt: return enc_.orGate(zero, negative).negated();
            }
        }
    }
    BitVec value = terms && !terms->empty() ? encodeSum(*terms) : enc_.mkConst(mpz_class(0), 1);
    const bool diag = xolver::config::read<xolver::config::ReadKind::Presence>("BB_ASSERT_DIAG");
    if (diag) {
        std::cerr << "[BB-ASSERT] rel=" << (int)c.rel
                  << " value_width=" << value.width()
                  << " poly=" << kernel_.toString(c.poly) << "\n";
        std::cerr.flush();
    }
    return enc_.relZero(value, c.rel);
}

void PolyBitBlaster::assertConstraint(const NormalizedNiaConstraint& c) {
    enc_.assertLit(encodeConstraint(c));
}

} // namespace xolver::bitblast
