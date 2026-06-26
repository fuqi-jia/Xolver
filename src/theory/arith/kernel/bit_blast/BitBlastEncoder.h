#pragma once

#include "sat/SatSolver.h"
#include "theory/arith/kernel/bit_blast/BitVec.h"
#include "expr/types.h"          // Relation
#include <gmpxx.h>
#include <cstdint>
#include <utility>
#include <unordered_map>

namespace xolver::bitblast {

// CNF encoder over an independent SAT instance. Two's-complement, width-growing
// arithmetic: add -> max(wa,wb)+1, mul -> wa+wb, so the encoded value is exact
// whenever leaf widths cover their domains. Non-owning reference to the SAT.
class BitBlastEncoder {
public:
    explicit BitBlastEncoder(SatSolver& sat);

    SatLit constTrue()  const { return true_; }
    SatLit constFalse() const { return false_; }

    BitVec mkConst(const mpz_class& v, unsigned minWidth = 0);
    BitVec mkVar(unsigned width);

    // Tseitin gates (each allocates one fresh var).
    SatLit andGate(SatLit a, SatLit b);
    SatLit orGate(SatLit a, SatLit b);
    SatLit xorGate(SatLit a, SatLit b);
    SatLit iteGate(SatLit s, SatLit t, SatLit e);

    // Arithmetic.
    BitVec add(const BitVec& a, const BitVec& b);    // width max+1
    BitVec neg(const BitVec& a);                     // width +1
    BitVec sub(const BitVec& a, const BitVec& b);
    BitVec mul(const BitVec& a, const BitVec& b);    // width wa+wb
    BitVec mulConst(const mpz_class& c, const BitVec& a);
    BitVec powConst(const BitVec& a, unsigned e);

    // Relations: every NIA constraint is `value rel 0`.
    SatLit isZero(const BitVec& a);
    SatLit eq(const BitVec& a, const BitVec& b);
    SatLit relZero(const BitVec& a, Relation rel);

    void assertLit(SatLit l);

    // Hard resource guard: cap the number of fresh SAT variables this encoder
    // will allocate. High-degree QF_NIA can blow the encoding past memory and
    // abort inside CaDiCaL with bad_alloc; once the budget is hit, freshVar()
    // stops allocating (returns the constant-false literal) and sets the
    // overflow flag, so the caller can bail to Unknown WITHOUT solving the
    // (now-incomplete) encoding. 0 = unlimited.
    void setVarBudget(uint64_t maxVars) { maxVars_ = maxVars; }
    bool overflowed() const { return over_; }
    uint64_t varCount() const { return varCount_; }

private:
    SatSolver& sat_;
    SatLit true_;
    SatLit false_;

    // Allocate one fresh SAT variable, honouring the var budget.
    SatLit freshVar();
    uint64_t maxVars_ = 0;     // 0 = unlimited
    uint64_t varCount_ = 0;
    bool over_ = false;

    // Structural hashing (AIG-style gate sharing): a Tseitin gate output is a
    // pure function of its (type, sorted operands), so identical sub-circuits —
    // rampant in bit-blasting (sign-extension partials in mul, repeated adder
    // bits) — collapse to ONE shared variable instead of a fresh var each call.
    // Exact (semantics-preserving), and a major SAT-var/clause reduction that
    // turns a ~10x-bloated multiplication encoding back to BLAN-tight. Per-
    // encoder (the encoder is constructed fresh per attempt), so cached literals
    // never leak across SAT instances. Key packs type(2) | loEnc(31) | hiEnc(31)
    // where enc = (var<<1)|sign; bit-blast vars are budget-bounded (<<2^30) so
    // the pack is collision-free. Opt-out: XOLVER_NIA_BB_NO_GATE_CACHE.
    uint64_t gateKey(unsigned type, SatLit a, SatLit b) const {
        uint64_t ae = (uint64_t(a.var) << 1) | (a.sign ? 1u : 0u);
        uint64_t be = (uint64_t(b.var) << 1) | (b.sign ? 1u : 0u);
        uint64_t lo = ae < be ? ae : be, hi = ae < be ? be : ae;
        return (uint64_t(type) << 62) | (lo << 31) | hi;
    }
    std::unordered_map<uint64_t, SatLit> gateCache_;
    bool gateCacheOn_ = true;

    static unsigned bitsForValue(const mpz_class& v);
    BitVec signExtend(const BitVec& a, unsigned width);
    std::pair<SatLit, SatLit> fullAdder(SatLit a, SatLit b, SatLit cin);
    BitVec addFixed(const BitVec& a, const BitVec& b, unsigned w); // truncates to w
    BitVec shiftLeft(const BitVec& a, unsigned k);                 // a * 2^k (exact, width +k)
    BitVec negFixed(const BitVec& a, unsigned w);                  // -a in width w
};

} // namespace xolver::bitblast
