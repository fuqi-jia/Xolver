#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include <algorithm>

namespace zolver::bitblast {

PolyBitBlaster::PolyBitBlaster(BitBlastEncoder& enc, PolynomialKernel& kernel,
                               const std::unordered_map<std::string, BitVec>& varBits)
    : enc_(enc), kernel_(kernel), varBits_(varBits) {}

BitVec PolyBitBlaster::encodeMonomial(const PolynomialKernel::MonomialTerm& m) {
    if (m.powers.empty()) return enc_.mkConst(m.coefficient);
    BitVec prod;
    bool first = true;
    for (const auto& pe : m.powers) {
        std::string name(kernel_.varName(pe.first));
        const BitVec& vb = varBits_.at(name);
        BitVec powered = enc_.powConst(vb, static_cast<unsigned>(pe.second));
        prod = first ? powered : enc_.mul(prod, powered);
        first = false;
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

} // namespace zolver::bitblast
