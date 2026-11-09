#pragma once

#include "search/lra/GeneralSimplex.h"
#include "algebra/linear/LinearExpr.h"
#include "ir/types.h"
#include <gmpxx.h>
#include <vector>
#include <unordered_set>
#include <string>

namespace xolver {

class LinearAtomManager;

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
 * Re-evaluates original source forms at canonical source coordinates.
 * Tableau display names and auxiliary row values do not establish identity
 * or replace this independent arithmetic check.
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
        const GeneralSimplex& gs, const LinearAtomManager& manager);

private:
    bool checkAtom(const ActiveLinearAtom& atom, const GeneralSimplex& gs,
                   const LinearAtomManager& manager);
    bool satisfiesRelation(const DeltaRational& val, Relation rel, bool value);
};

} // namespace xolver
