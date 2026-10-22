#pragma once

#include "search/nia/NiaTypes.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "algebra/poly/PolynomialKernel.h"
#include <cstdint>
#include <vector>

namespace xolver {

/**
 * Refute integer constraints using constant-modulus arithmetic.
 *
 * Recognizes a = n*q + r with 0 <= r < n, eliminates suitable quotient
 * occurrences, and builds simple polynomial definitions. Enumerates a modular
 * relaxation within its resource limits; a conflict from this path must also
 * pass independent enumeration of the original normalized equalities and
 * relevant remainder constraints.
 *
 * For recognized Newton chains modulo a prime power, a separate path checks
 * polynomial identities and the small base congruence before lifting them.
 * Neither path produces a SAT result. An unhandled structure, inconclusive
 * certificate or resource limit leaves the remaining solver stages to run.
 */
class ModularResidueReasoner {
public:
    explicit ModularResidueReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints);

    // Largest modulus the reasoner will enumerate (default 1<<18). A constant
    // modulus above this (e.g. 2^256) is skipped — that needs Hensel lifting.
    // Overrides the env-derived default; tests and callers can pin it.
    void setModulusCap(uint64_t cap) { modulusCap_ = cap; }
    // Hard cap on the total number of residue assignments enumerated for a
    // single modulus (default 1<<24). Above this, the modulus is skipped.
    void setEnumBudget(uint64_t budget) { enumBudget_ = budget; }

private:
    PolynomialKernel& kernel_;
    // Base resource caps, read through the typed runtime configuration:
    //   XOLVER_NIA_MODULAR_MODULUS_CAP   (default 1<<18 = 262144)
    //   XOLVER_NIA_MODULAR_ENUM_BUDGET   (default 1<<24 ≈ 16.7M)
    // Sound — UNSAT-only, and over-budget moduli are skipped (never wrong).
    // Verified Newton lifting can handle prime-power goals beyond the cap.
    uint64_t modulusCap_;
    uint64_t enumBudget_;

    // Wall-clock-scaled views of modulusCap_/enumBudget_. With
    // XOLVER_WALLCLOCK_SCALE off (default), return the base cap unchanged.
    // With it on + an active deadline, grow proportionally to remaining time.
    mpz_class currentModulusCap() const;
    mpz_class currentEnumBudget() const;
};

} // namespace xolver
