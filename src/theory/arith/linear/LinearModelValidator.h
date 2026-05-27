#pragma once

#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/linear/LinearExpr.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>

namespace zolver {

/**
 * ActiveLinearAtom: record of an asserted theory literal for validation.
 */
struct ActiveLinearAtom {
    ExprId exprId;
    int auxVar;      // GeneralSimplex aux var: aux = lhs - rhs
    Relation rel;
    bool value;      // true = original relation, false = negated relation
    LinearFormKey lhs;  // left-hand side terms
    mpq_class rhs;      // right-hand side constant
    SatLit lit;         // original SAT literal (for lemma construction)
};

/**
 * DiseqValidationInfo for model validation.
 */
struct DiseqValidationInfo {
    int auxVar;
};

/**
 * LinearModelValidator: validates that a GeneralSimplex model satisfies
 * all active LIA constraints.
 *
 * Uses aux variables for evaluation: each atom's aux var represents
 * aux = lhs - rhs, so checking the aux value against 0 is equivalent
 * to checking the original constraint.
 */
class LinearModelValidator {
public:
    /**
     * Validate the current GeneralSimplex model.
     *
     * Checks:
     * 1. All integer variables have integer values.
     * 2. All disequality obligations are satisfied (aux != 0).
     * 3. All active atoms are satisfied under their asserted value.
     *
     * Returns true if validation passes.
     */
    bool validateLiaModel(
        const std::vector<ActiveLinearAtom>& activeAtoms,
        const std::vector<DiseqValidationInfo>& disequalities,
        const std::unordered_set<int>& integerVars,
        const GeneralSimplex& gs);

private:
    bool checkAtom(const ActiveLinearAtom& atom, const GeneralSimplex& gs,
                   const std::unordered_map<std::string, int>& nameToIdx);
    bool satisfiesRelation(const DeltaRational& val, Relation rel, bool value);
};

} // namespace zolver
