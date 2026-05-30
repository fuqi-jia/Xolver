#pragma once

#include "expr/ir.h"
#include <string_view>
#include <unordered_set>

namespace xolver {

/**
 * ZoharBwiAxiomEmitter (Phase 1 of the Zohar bit-width-independent plugin).
 *
 * Detects the Zohar/Niemetz CADE-27 (2019) bit-width-independent QF_UFNIA
 * encoding (uninterpreted `pow2`, `intand`, `intor`, `intxor` functions used
 * with their standard interpretations) and injects axiom assertions for the
 * `pow2` UF symbol so the NIA engine can reason about it instead of treating
 * it as opaque.
 *
 * Phase 1 scope (minimum-viable, sound):
 *
 *   - Ground:   (= (pow2 0) 1)
 *   - Per-term: (=> (>= t 0) (>= (pow2 t) 1))    for each unique (pow2 t)
 *               appearing in the assertions
 *
 * Each axiom is mathematically valid for the STANDARD interpretation
 * pow2(n) = 2^n on n >= 0. The plugin is gated on detecting the standard
 * Zohar signature (a `pow2` UF symbol of type (Int) -> Int actually applied
 * in the formula); a case that uses `pow2` with a non-standard interpretation
 * would still be sound because we only assert true facts about pow2 under the
 * standard semantics — those facts can rule out non-standard models, but
 * agreement with z3/cvc5 (which use the standard semantics) is preserved.
 *
 * Phase 2 (planned, not in this class yet): trigger-based recursion
 * `pow2(k+1) = 2*pow2(k)` and intand/intor/intxor bounded axioms, with a
 * per-cb_propagate budget and cap on chain depth.
 *
 * Sound: only ADDS assertions, never removes or rewrites existing ones.
 * Empty no-op when no `pow2` UF symbol is present in the formula.
 *
 * Gate: `XOLVER_NIA_ZOHAR_PLUGIN` env var, default-OFF. Run inside the
 * frontend preprocess pipeline after FormulaRewriter so the search for `pow2`
 * terms sees the post-rewrite shape.
 */
class ZoharBwiAxiomEmitter {
public:
    explicit ZoharBwiAxiomEmitter(CoreIr& ir, SortId boolSortId);

    /** Run detection + emission. Returns true iff at least one axiom was added. */
    bool run();

    /** Whether the Zohar signature was found at all (independent of emission count). */
    bool detected() const { return detected_; }

    /** How many axioms were appended to the assertion list. */
    size_t axiomCount() const { return axiomCount_; }

private:
    /** Walk all assertions and collect every distinct (pow2 t) ExprId. */
    void collectPow2Terms(std::unordered_set<ExprId>& out) const;

    /** True when `node` is a UFApply whose function-symbol name matches `name`. */
    static bool isUfApplyNamed(const CoreExpr& node, std::string_view name);

    /** Build literals + axiom forms. */
    ExprId mkConstInt(int64_t v);
    ExprId mkGeq(ExprId a, ExprId b);
    ExprId mkEq(ExprId a, ExprId b);
    ExprId mkImplies(ExprId a, ExprId b);
    ExprId mkPow2(ExprId arg, SortId intSort);

    /** Memoized DFS over all assertions. */
    void visit(ExprId root, std::unordered_set<ExprId>& visited,
               std::unordered_set<ExprId>& pow2Terms) const;

    CoreIr& ir_;
    SortId boolSortId_;
    SortId intSortId_;
    bool detected_ = false;
    size_t axiomCount_ = 0;
};

} // namespace xolver
