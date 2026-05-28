#pragma once

// RealAlgebraicOps — the algebraic-number operations behind RealValue, declared
// here WITHOUT any libpoly include so that util/RealValue.cpp (libpoly-free) can
// call them.  The implementation lives in
// src/theory/arith/nra/backend/LibpolyAlgebraic.cpp, the single translation
// unit that pulls in <polyxx.h>.  This keeps the dependency edge pointing the
// right way: util declares the contract, the nra backend implements it.
//
// Every operation that receives at least one Algebraic operand routes here;
// RealValue keeps a pure-GMP fast path for Rational⊕Rational.  Results collapse
// back to Rational whenever libpoly reports the value is rational (so e.g.
// √2·√2 → 2).

#include "util/RealValue.h"

namespace xolver::realalg {

// Binary arithmetic. At least one operand is expected to be Algebraic (the
// Rational⊕Rational case is handled directly in RealValue); however these are
// correct for any operands. `div` throws std::domain_error on a zero divisor.
RealValue add(const RealValue& a, const RealValue& b);
RealValue sub(const RealValue& a, const RealValue& b);
RealValue mul(const RealValue& a, const RealValue& b);
RealValue div(const RealValue& a, const RealValue& b);
RealValue neg(const RealValue& a);

// Total-order comparison: -1, 0, +1.
int compare(const RealValue& a, const RealValue& b);

// Sign of a single value: -1, 0, +1.
int sign(const RealValue& a);

// Integer predicates on an Algebraic value (RealValue handles the Rational
// case itself).
bool isExactInteger(const RealValue& a);
mpz_class floorOf(const RealValue& a);
mpz_class ceilOf(const RealValue& a);

} // namespace xolver::realalg
