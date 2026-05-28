#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <cstdint>
#include <vector>

namespace xolver {

/**
 * ModularResidueReasoner (L3): sound UNSAT refutation for NIA systems that
 * carry a constant power-of-two modulus, the canonical shape of EVM /
 * modular-inverse benchmarks (`... mod 2^k`).
 *
 * Soundness (NIA invariant 7 — UNSAT only, never SAT):
 *   Any integer solution of the constraint system projects to a solution of
 *   the system reduced modulo m. Hence if the *reduced* system has no solution
 *   over Z/m, the original has none either => UNSAT. The reasoner ONLY ever
 *   concludes UNSAT this way; it never claims SAT and never refutes from an
 *   incomplete check.
 *
 * How it stays tractable (the EVM timeout wall):
 *   Bit-blasting `mod 2^256` enumerates the full 2^256 domain. Instead this
 *   reasoner
 *     1. recognises `div`/`mod`-lowered groups `a = n*q + r, 0<=r<n` (n a
 *        power of two) and *eliminates* the quotient q by the EXACT identity
 *        n*q = a - r (integer, not modular — so it is loss-free), and
 *        derives the remainder r = a mod n;
 *     2. solves the remaining linear definitions (`v = poly(others)`), leaving
 *        only a small set of "primary" free variables;
 *     3. enumerates the primary variables over Z/m (m the constant modulus,
 *        capped) and checks every equality (== 0 mod m) plus every
 *        exactly-pinned remainder disequality. If no residue assignment is a
 *        model, the system is UNSAT.
 *
 *   For modInv8 (assert (= 1 (mod (* d inv2) 256))) this collapses a
 *   12-variable system to enumerating `d` over Z/256.
 *
 * If anything cannot be handled soundly (non-power-of-two modulus, modulus
 * over the cap, a dependency cycle, an undetermined variable, enumeration over
 * budget) the reasoner returns NoChange and the pipeline falls through. It is
 * therefore always safe to enable, and complements
 * AlgebraicIntegerReasoner::checkModular (which only handled <=2 variables and
 * tiny fixed moduli, and was blind to the div/mod auxiliary variables).
 */
class ModularResidueReasoner {
public:
    explicit ModularResidueReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints);

    // Largest modulus the reasoner will enumerate (default 1<<16). A constant
    // modulus above this (e.g. 2^256) is skipped — that needs Hensel lifting.
    void setModulusCap(uint64_t cap) { modulusCap_ = cap; }
    // Hard cap on the total number of residue assignments enumerated for a
    // single modulus (default 1<<20). Above this, the modulus is skipped.
    void setEnumBudget(uint64_t budget) { enumBudget_ = budget; }

private:
    PolynomialKernel& kernel_;
    uint64_t modulusCap_ = (1u << 16);
    uint64_t enumBudget_ = (1u << 20);
};

} // namespace xolver
