#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include <algorithm>

namespace nlcolver::bitblast {

BitBlastEncoder::BitBlastEncoder(SatSolver& sat) : sat_(sat) {
    SatVar t = sat_.newVar();
    sat_.addClause({SatLit::positive(t)});   // clamp t = true
    true_  = SatLit::positive(t);
    false_ = SatLit::negative(t);
}

unsigned BitBlastEncoder::bitsForValue(const mpz_class& v) {
    unsigned w = 1;
    while (true) {
        mpz_class lo = -(mpz_class(1) << (w - 1));
        mpz_class hi =  (mpz_class(1) << (w - 1)) - 1;
        if (v >= lo && v <= hi) return w;
        ++w;
    }
}

BitVec BitBlastEncoder::mkConst(const mpz_class& v, unsigned minWidth) {
    unsigned w = std::max(minWidth, bitsForValue(v));
    BitVec bv;
    bv.isConst = true;
    bv.constValue = v;
    bv.bits.resize(w);
    mpz_class t = v;
    if (t < 0) t += (mpz_class(1) << w);     // two's-complement pattern
    for (unsigned i = 0; i < w; ++i) {
        bv.bits[i] = mpz_tstbit(t.get_mpz_t(), i) ? true_ : false_;
    }
    return bv;
}

BitVec BitBlastEncoder::mkVar(unsigned width) {
    BitVec bv;
    bv.bits.resize(width);
    for (unsigned i = 0; i < width; ++i) bv.bits[i] = SatLit::positive(sat_.newVar());
    return bv;
}

SatLit BitBlastEncoder::andGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a.negated(), b.negated(), c});
    sat_.addClause({a, c.negated()});
    sat_.addClause({b, c.negated()});
    return c;
}

SatLit BitBlastEncoder::orGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a.negated(), c});
    sat_.addClause({b.negated(), c});
    return c;
}

SatLit BitBlastEncoder::xorGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a.negated(), b.negated(), c.negated()});
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a, b.negated(), c});
    sat_.addClause({a.negated(), b, c});
    return c;
}

SatLit BitBlastEncoder::iteGate(SatLit s, SatLit t, SatLit e) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({s.negated(), t.negated(), c});
    sat_.addClause({s.negated(), t, c.negated()});
    sat_.addClause({s, e.negated(), c});
    sat_.addClause({s, e, c.negated()});
    return c;
}

void BitBlastEncoder::assertLit(SatLit l) { sat_.addClause({l}); }

// --- arithmetic and relations are added in later tasks ---

} // namespace nlcolver::bitblast
