#pragma once

#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"   // NormalizedNiaConstraint
#include "expr/types.h"                                  // VarId
#include <map>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace xolver::bitblast {

// Lowers a normalized NIA constraint `p rel 0` to CNF: decomposes p into
// monomials (kernel.terms), encodes each as coeff * prod(var^exp), then sums
// them with Greedy-Addition sorting (fold the two narrowest first) before
// asserting `relZero(sum, rel)`.
class PolyBitBlaster {
public:
    PolyBitBlaster(BitBlastEncoder& enc, PolynomialKernel& kernel,
                   const std::unordered_map<std::string, BitVec>& varBits);

    void assertConstraint(const NormalizedNiaConstraint& c);

    // Encode a polynomial to its value bit-vector (used by assertConstraint).
    BitVec encodePoly(PolyId p);

    // Test-only: width of the encoded value bit-vector.
    unsigned encodePolyWidth(PolyId p) { return encodePoly(p).width(); }

private:
    BitVec encodeMonomial(const PolynomialKernel::MonomialTerm& m);

    BitBlastEncoder& enc_;
    PolynomialKernel& kernel_;
    const std::unordered_map<std::string, BitVec>& varBits_;

    // Common-subexpression elimination for variable products (BLAN's mkInnerVar
    // cache). Keyed by the sorted (VarId, cumulative-exponent) prefix; monomials
    // are built in canonical VarId order so shared leading factors (e.g. a var
    // appearing in hundreds of monomials) are encoded ONCE. Without this the
    // same sub-products are re-blasted per monomial — a quadratic gate blow-up
    // that OOMs on high-degree QF_NIA. The cache holds BitVecs over the current
    // encoder's SAT instance, so it lives for one solve() iteration (one encoder).
    std::map<std::vector<std::pair<VarId, int>>, BitVec> productCache_;
};

} // namespace xolver::bitblast
