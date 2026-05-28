#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include <algorithm>

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
    return enc_.mulConst(m.coefficient, prod);
}

BitVec PolyBitBlaster::encodePoly(PolyId p) {
    auto termsOpt = kernel_.terms(p);
    if (!termsOpt || termsOpt->empty()) return enc_.mkConst(mpz_class(0), 1);

    std::vector<BitVec> monos;
    monos.reserve(termsOpt->size());
    for (const auto& m : *termsOpt) monos.push_back(encodeMonomial(m));

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

void PolyBitBlaster::assertConstraint(const NormalizedNiaConstraint& c) {
    BitVec value = encodePoly(c.poly);
    enc_.assertLit(enc_.relZero(value, c.rel));
}

} // namespace xolver::bitblast
