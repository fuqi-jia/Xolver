#pragma once

#include "search/nia/NiaTypes.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/core/DomainStore.h"
#include "contracts/TheorySolver.h"
#include "search/coordination/TheoryAtomRegistry.h"

namespace xolver {

/**
 * AlgebraicIntegerReasoner: square rules, GCD conflicts, factor lemmas,
 * and modular reasoning for NIA.
 */
class AlgebraicIntegerReasoner {
public:
    explicit AlgebraicIntegerReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains,
                           TheoryLemmaStorage& lemmaDb);

private:
    PolynomialKernel& kernel_;

    // Square rules: x^2 < 0 → UNSAT, x^2 <= 0 → x = 0
    NiaReasoningResult checkSquareRules(const NormalizedNiaConstraint& c,
                                         DomainStore& domains);

    // GCD equality conflict: 2x^2 + 4y = 3 → UNSAT
    NiaReasoningResult checkGcdConflict(const NormalizedNiaConstraint& c);

    // Factor rules: p*q = 0 → lemma (split lemma, V2)
    NiaReasoningResult checkFactorRules(const NormalizedNiaConstraint& c,
                                         TheoryLemmaStorage& lemmaDb);

    // Factor direct conflict: p*q = 0 ∧ p≠0 ∧ q≠0 → UNSAT
    NiaReasoningResult checkFactorDirectConflict(
        const std::vector<NormalizedNiaConstraint>& constraints);

    // Modular reasoning: x^2 = 2 → mod-4 UNSAT
    NiaReasoningResult checkModular(const std::vector<NormalizedNiaConstraint>& equalities);

    // Check if polynomial is syntactically a sum of squares
    bool isSumOfSquares(PolyId poly, std::vector<PolyId>& squares) const;

    // Evaluate polynomial mod m at a residue assignment
    bool evaluateMod(PolyId poly,
                     const std::vector<std::string>& vars,
                     const std::vector<int>& residues,
                     int modulus,
                     int& result) const;
};

} // namespace xolver
