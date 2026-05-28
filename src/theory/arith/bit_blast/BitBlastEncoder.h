#pragma once

#include "sat/SatSolver.h"
#include "theory/arith/bit_blast/BitVec.h"
#include "expr/types.h"          // Relation
#include <gmpxx.h>
#include <cstdint>
#include <utility>

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

    static unsigned bitsForValue(const mpz_class& v);
    BitVec signExtend(const BitVec& a, unsigned width);
    std::pair<SatLit, SatLit> fullAdder(SatLit a, SatLit b, SatLit cin);
    BitVec addFixed(const BitVec& a, const BitVec& b, unsigned w); // truncates to w
    BitVec shiftLeft(const BitVec& a, unsigned k);                 // a * 2^k (exact, width +k)
    BitVec negFixed(const BitVec& a, unsigned w);                  // -a in width w
};

} // namespace xolver::bitblast
