// Farkas-Or Model Constructor — detector (Phase 0).
//
// Scans the original CoreIr assertion list and identifies:
//   - Top-level Or blocks whose every child is a Farkas-shaped And
//     (one or more λ-non-negativity atoms + linear-in-λ equalities /
//     inequalities)
//   - Small-domain global vars detected from outer bound conjunctions
//   - Outer (non-Or) assertions kept as residuals
//
// Phase 0 ONLY detects + dumps. No model construction, no solving. The
// purpose is to validate that Stroeder/VeryMax/Farkas-shaped inputs are
// recognized and to surface their structure to humans before we implement
// the harder phases.

#pragma once

#include "expr/ir.h"
#include "theory/arith/nia/farkas/FarkasOrTypes.h"
#include <string>

namespace xolver::farkas {

class FarkasOrDetector {
public:
    explicit FarkasOrDetector(const CoreIr& ir) : ir_(ir) {}

    // Walk current assertions, build a FarkasProfile. Cheap: O(assertion-tree).
    FarkasProfile detect() const;

    // Pretty-printer for human inspection (XOLVER_NIA_FARKAS_DUMP).
    std::string dump(const FarkasProfile& p) const;

private:
    const CoreIr& ir_;

    // Try to recognize a top-level Or as a Farkas-Or block. Each child of
    // the Or must be an And that classifies as a FarkasBranch (lambdas
    // non-empty AND linear-in-λ shape recognized; otherwise the block is
    // rejected and the assertion goes to outerAssertions).
    std::optional<FarkasOrBlock> tryClassifyOr(ExprId orId) const;

    // Classify a single Farkas branch inside an Or.
    FarkasBranch classifyAnd(ExprId andId) const;

    // λ-detection: an atom `Geq(v, 0)` where v is a Variable.
    // Returns the var name on success.
    std::optional<std::string> extractLambdaVar(ExprId atomId) const;

    // Bound extraction: if expr is `(and (>= v c) (<= v c'))` or
    // `(and (<= c v) (<= v c'))` style, populate boundedGlobals.
    // Recurses lightly so chained `And(And(a, b), c)` work too.
    // Returns true if at least one bound pair was extracted.
    bool extractBoundsFromAnd(ExprId andId, FarkasProfile& p) const;

    // Atom-shape classification used inside an And branch.
    // Returns true if the atom is linear-in-λ-shaped (best effort).
    bool isLinearInLambdaEquality(ExprId atomId,
                                  const std::vector<std::string>& lambdas) const;
    bool isLinearInLambdaInequality(ExprId atomId,
                                    const std::vector<std::string>& lambdas) const;

    // Walk a Sub/Add/Mul/Neg/Variable/Const tree to determine if every monomial
    // is `c * λ_j` (degree 1 in some λ) or `c * λ_j * v_k` (bilinear λ × non-λ).
    // We don't yet construct the coefficient matrix — just detect shape.
    bool monomialsLinearInLambda(ExprId polyId,
                                 const std::vector<std::string>& lambdas) const;

    // Discovery: collect every var that appears in λ·v bilinear monomials
    // across Farkas branches. The ones with bounded domain go to
    // boundedGlobals; the rest become unboundedCT.
    void classifyBilinearCovars(FarkasProfile& p) const;

    // Helpers: extract var name / int constant from an ExprId.
    std::optional<std::string> asVarName(ExprId id) const;
    std::optional<mpz_class>   asIntConst(ExprId id) const;
    bool isZeroConst(ExprId id) const;
};

} // namespace xolver::farkas
