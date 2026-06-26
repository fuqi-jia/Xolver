#include "theory/arith/kernel/bit_blast/BitBlastEncoder.h"
#include "util/EnvParam.h"
#include <algorithm>
#include <cstdlib>

namespace xolver::bitblast {

BitBlastEncoder::BitBlastEncoder(SatSolver& sat) : sat_(sat) {
    SatVar t = sat_.newVar();
    sat_.addClause({SatLit::positive(t)});   // clamp t = true
    true_  = SatLit::positive(t);
    false_ = SatLit::negative(t);
    gateCacheOn_ = (!xolver::env::diag("XOLVER_NIA_BB_NO_GATE_CACHE"));
}

// One fresh SAT variable, capped by maxVars_. Once the budget is exhausted we
// stop creating variables and return the constant-false literal, setting over_;
// the resulting encoding is incomplete and MUST NOT be solved (the caller
// checks overflowed() and bails to Unknown). This is what turns a degree-5
// QF_NIA encoding blow-up into a clean Unknown instead of an OOM abort.
SatLit BitBlastEncoder::freshVar() {
    if (maxVars_ != 0 && varCount_ >= maxVars_) { over_ = true; return false_; }
    ++varCount_;
    return SatLit::positive(sat_.newVar());
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
    for (unsigned i = 0; i < width; ++i) bv.bits[i] = freshVar();
    return bv;
}

SatLit BitBlastEncoder::andGate(SatLit a, SatLit b) {
    if (over_) return false_;        // budget exhausted: no more gates/clauses
    // Constant folding (BLAN transformer simplifier): skip the fresh var/clauses
    // when an input is constant or the inputs are (anti)identical. Bit-blasting
    // produces MANY constant inputs (padding, sign-extension, zero partials), so
    // this is the dominant SAT-var reduction. Exact (semantics-preserving).
    if (a == false_ || b == false_) return false_;
    if (a == true_)  return b;
    if (b == true_)  return a;
    if (a == b)      return a;
    if (a == b.negated()) return false_;
    uint64_t key = 0;
    if (gateCacheOn_) {
        key = gateKey(0, a, b);
        auto it = gateCache_.find(key);
        if (it != gateCache_.end()) return it->second;
    }
    SatLit c = freshVar();
    sat_.addClause({a.negated(), b.negated(), c});
    sat_.addClause({a, c.negated()});
    sat_.addClause({b, c.negated()});
    if (gateCacheOn_ && !over_) gateCache_[key] = c;
    return c;
}

SatLit BitBlastEncoder::orGate(SatLit a, SatLit b) {
    if (over_) return false_;        // budget exhausted: no more gates/clauses
    if (a == true_ || b == true_) return true_;
    if (a == false_) return b;
    if (b == false_) return a;
    if (a == b)      return a;
    if (a == b.negated()) return true_;
    uint64_t key = 0;
    if (gateCacheOn_) {
        key = gateKey(1, a, b);
        auto it = gateCache_.find(key);
        if (it != gateCache_.end()) return it->second;
    }
    SatLit c = freshVar();
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a.negated(), c});
    sat_.addClause({b.negated(), c});
    if (gateCacheOn_ && !over_) gateCache_[key] = c;
    return c;
}

SatLit BitBlastEncoder::xorGate(SatLit a, SatLit b) {
    if (over_) return false_;        // budget exhausted: no more gates/clauses
    if (a == false_) return b;
    if (b == false_) return a;
    if (a == true_)  return b.negated();
    if (b == true_)  return a.negated();
    if (a == b)      return false_;
    if (a == b.negated()) return true_;
    uint64_t key = 0;
    if (gateCacheOn_) {
        key = gateKey(2, a, b);
        auto it = gateCache_.find(key);
        if (it != gateCache_.end()) return it->second;
    }
    SatLit c = freshVar();
    sat_.addClause({a.negated(), b.negated(), c.negated()});
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a, b.negated(), c});
    sat_.addClause({a.negated(), b, c});
    if (gateCacheOn_ && !over_) gateCache_[key] = c;
    return c;
}

SatLit BitBlastEncoder::iteGate(SatLit s, SatLit t, SatLit e) {
    if (over_) return false_;        // budget exhausted: no more gates/clauses
    if (s == true_)  return t;
    if (s == false_) return e;
    if (t == e)      return t;
    if (t == true_  && e == false_) return s;
    if (t == false_ && e == true_)  return s.negated();
    if (t == true_)  return orGate(s, e);          // s ? 1 : e
    if (e == false_) return andGate(s, t);         // s ? t : 0
    if (t == false_) return andGate(s.negated(), e);
    if (e == true_)  return orGate(s.negated(), t);
    SatLit c = freshVar();
    sat_.addClause({s.negated(), t.negated(), c});
    sat_.addClause({s.negated(), t, c.negated()});
    sat_.addClause({s, e.negated(), c});
    sat_.addClause({s, e, c.negated()});
    return c;
}

void BitBlastEncoder::assertLit(SatLit l) { sat_.addClause({l}); }

BitVec BitBlastEncoder::signExtend(const BitVec& a, unsigned width) {
    BitVec r = a;
    SatLit s = a.sign();
    while (r.bits.size() < width) r.bits.push_back(s);
    return r;
}

std::pair<SatLit, SatLit> BitBlastEncoder::fullAdder(SatLit a, SatLit b, SatLit cin) {
    SatLit axb  = xorGate(a, b);
    SatLit sum  = xorGate(axb, cin);
    SatLit ab   = andGate(a, b);
    SatLit acin = andGate(axb, cin);
    SatLit cout = orGate(ab, acin);
    return {sum, cout};
}

BitVec BitBlastEncoder::addFixed(const BitVec& a, const BitVec& b, unsigned w) {
    BitVec ea = signExtend(a, w), eb = signExtend(b, w);
    BitVec r; r.bits.resize(w);
    SatLit cin = false_;
    for (unsigned i = 0; i < w; ++i) {
        if (over_) break;        // budget exhausted: stop emitting adders
        auto sc = fullAdder(ea.bits[i], eb.bits[i], cin);
        r.bits[i] = sc.first;
        cin = sc.second;
    }
    return r;   // final carry dropped (caller sized w to avoid overflow)
}

BitVec BitBlastEncoder::add(const BitVec& a, const BitVec& b) {
    unsigned w = std::max(a.width(), b.width()) + 1;
    return addFixed(a, b, w);
}

BitVec BitBlastEncoder::neg(const BitVec& a) {
    // Two's-complement negate: invert bits, then +1, in width a.width()+1
    // (one extra bit so that -(-2^(w-1)) = 2^(w-1) is representable).
    BitVec inv; inv.bits.resize(a.width());
    for (unsigned i = 0; i < a.width(); ++i) inv.bits[i] = a.bits[i].negated();
    return addFixed(inv, mkConst(mpz_class(1)), a.width() + 1);
}

BitVec BitBlastEncoder::sub(const BitVec& a, const BitVec& b) {
    return add(a, neg(b));
}

SatLit BitBlastEncoder::isZero(const BitVec& a) {
    SatLit acc = a.bits[0];
    for (unsigned i = 1; i < a.width(); ++i) acc = orGate(acc, a.bits[i]);
    return acc.negated();
}

BitVec BitBlastEncoder::shiftLeft(const BitVec& a, unsigned k) {
    if (k == 0) return a;
    BitVec r;
    r.bits.reserve(a.width() + k);
    for (unsigned i = 0; i < k; ++i) r.bits.push_back(false_);   // low k bits = 0
    for (unsigned i = 0; i < a.width(); ++i) r.bits.push_back(a.bits[i]);
    return r;   // exact a * 2^k (two's-complement, no truncation)
}

BitVec BitBlastEncoder::negFixed(const BitVec& a, unsigned w) {
    BitVec inv; inv.bits.resize(a.width());
    for (unsigned i = 0; i < a.width(); ++i) inv.bits[i] = a.bits[i].negated();
    return addFixed(inv, mkConst(mpz_class(1)), w);   // ~a + 1, truncated to w
}

// Bit-identical operands: same SAT literal at every position. Distinct encoded
// variables never share literals, so this holds iff a and b denote the SAME
// value (the x*x square case, where powConst passes one BitVec as both args).
static bool sameBits(const BitVec& a, const BitVec& b) {
    if (a.width() != b.width()) return false;
    for (unsigned i = 0; i < a.width(); ++i)
        if (a.bits[i].var != b.bits[i].var || a.bits[i].sign != b.bits[i].sign)
            return false;
    return true;
}

// Variable * variable.  Faithful port of BLAN's Multiply structure onto the
// two's-complement BitVec: partial products are generated ONLY over the NARROWER
// operand's bits (BLAN's `varmin`), not over the sign-extended sum width — so a
// chained product like (X:2w)*(a:w) costs w partials, not 3w.  The multiplier's
// sign bit (MSB) carries negative weight, so that one partial is subtracted.
BitVec BitBlastEncoder::mul(const BitVec& a, const BitVec& b) {
    // Constant folding (BLAN Multiply special-cases + MultiplyInt).
    if (a.isConst) return mulConst(a.constValue, b);
    if (b.isConst) return mulConst(b.constValue, a);

    const BitVec& X = (a.width() >= b.width()) ? a : b;   // multiplicand (wider)
    const BitVec& Y = (a.width() >= b.width()) ? b : a;   // multiplier  (narrower)
    unsigned w  = a.width() + b.width();
    unsigned wy = Y.width();
    BitVec ex  = signExtend(X, w);
    BitVec acc = mkConst(mpz_class(0), w);
    for (unsigned i = 0; i < wy; ++i) {
        if (over_) break;        // budget exhausted: stop emitting partials
        // addend = (Y[i] ? (X << i) : 0); bits [0,i) are structurally zero.
        BitVec addend; addend.bits.resize(w);
        for (unsigned j = 0; j < w; ++j)
            addend.bits[j] = (j >= i) ? andGate(ex.bits[j - i], Y.bits[i]) : false_;
        if (i + 1 == wy) addend = negFixed(addend, w);   // sign bit: subtract
        acc = addFixed(acc, addend, w);
    }
    // BLAN square optimisation (Multiply: var1==var2 -> signBit=0). x*x is a
    // perfect square, hence >= 0. With w = wa+wb we have x^2 < 2^(w-1), so the
    // result's sign bit is 0 in every model; pinning it to 0 prunes the
    // spurious-negative half of the search and can never remove a valid model.
    if (sameBits(a, b)) assertLit(acc.sign().negated());
    return acc;
}

// Constant * variable.  BLAN MultiplyInt: shift-add over the SET BITS of |c|
// (one pure shift of `a` per set bit, no multiplier circuit), negate if c<0.
// This is the dominant win for polynomial bodies full of `coeff * monomial`.
BitVec BitBlastEncoder::mulConst(const mpz_class& c, const BitVec& a) {
    if (c == 0) return mkConst(mpz_class(0), 1);
    if (a.isConst) return mkConst(c * a.constValue);
    if (c == 1)  return a;
    if (c == -1) return neg(a);
    mpz_class ac = abs(c);
    BitVec acc;
    bool first = true;
    size_t nbits = mpz_sizeinbase(ac.get_mpz_t(), 2);
    for (size_t k = 0; k < nbits; ++k) {
        if (mpz_tstbit(ac.get_mpz_t(), k)) {
            BitVec sh = shiftLeft(a, static_cast<unsigned>(k));   // a * 2^k
            acc = first ? sh : add(acc, sh);
            first = false;
        }
    }
    if (c < 0) acc = neg(acc);
    return acc;
}

BitVec BitBlastEncoder::powConst(const BitVec& a, unsigned e) {
    if (e == 0) return mkConst(mpz_class(1));
    BitVec r = a;
    // Each step multiplies the growing accumulator by the narrow base `a`, so
    // mul() uses a's width as the partial-product count (BLAN varmin behaviour).
    for (unsigned i = 1; i < e; ++i) r = mul(r, a);
    return r;
}

SatLit BitBlastEncoder::eq(const BitVec& a, const BitVec& b) {
    return isZero(sub(a, b));
}

SatLit BitBlastEncoder::relZero(const BitVec& a, Relation rel) {
    SatLit z = isZero(a);   // a == 0
    SatLit s = a.sign();    // a < 0  (exact, since `a` holds the value at full width)
    switch (rel) {
        case Relation::Eq:  return z;
        case Relation::Neq: return z.negated();
        case Relation::Lt:  return s;
        case Relation::Leq: return orGate(s, z);
        case Relation::Gt:  return andGate(s.negated(), z.negated());
        case Relation::Geq: return s.negated();
    }
    return z;
}

} // namespace xolver::bitblast
