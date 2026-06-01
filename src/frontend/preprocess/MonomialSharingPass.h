#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * MonomialSharingPass (H2, master 2026-06-01 audit).
 *
 * Replaces structurally-shared nonlinear monomials with a fresh integer/real
 * variable, anchored by ONE definitional assertion `m_<n> = (* x y ...)` per
 * shared monomial. Targets the case master flagged: a formula whose `(* x y)`
 * appears in N atoms causes the IncrementalLinearizer to emit N cut lemmas
 * (same content, different attribution via the per-atom cache key
 * `(aux, c.reason, bounds, idx)`) — wasting per-atom Standard-effort work
 * proportional to the multiplicity. After sharing, all N atoms reference a
 * single linear variable m_<n>, and the linearizer sees exactly ONE
 * nonlinear constraint (the definition); cut lemmas emit once.
 *
 * SOUNDNESS (the invariant master called out as critical):
 *   The definitional assertion m_<n> = (* x y) is added as a regular
 *   theory atom; the NIA solver still enforces it. We never eliminate
 *   nonlinearity — we only NAME it. Under any model M satisfying the
 *   rewritten formula, M(m_<n>) = M(x)*M(y) by construction, so the
 *   substitution is truth-preserving. Sat models from the rewritten
 *   formula validate against the ORIGINAL formula (ModelValidator
 *   evaluates the original assertions, which still type-check; the
 *   m_<n> entries are extra model points that ModelValidator ignores
 *   if they don't appear in the original).
 *
 * Scope:
 *   Only runs at base scope (no incremental push/pop): the substitution
 *   is global. Restricted to nonlinear arith logics (NIA/NIRA/NRA/UFNIA/
 *   UFNRA) — the pass is moot on linear-only logics. The frontend
 *   AtomNormalizer runs after this pass, so the m_<n> variables enter
 *   the SAT/theory layer like any other.
 *
 * Gating: XOLVER_PP_MONOMIAL_SHARE (default-OFF).
 */
class MonomialSharingPass {
public:
    MonomialSharingPass(CoreIr& ir, SortId intSort, SortId realSort, SortId boolSort);

    // Scan IR assertions for nonlinear Mul ExprIds with reference count >= 2
    // across the assertion DAG; pre-build the substitution map. Returns the
    // count of monomials selected for sharing. Run() is non-mutating; call
    // commit() to actually rewrite assertions and append the definitional
    // assertions.
    size_t run();

    // Apply the substitution: rewrite every assertion via memoized DAG walk,
    // then append the m_<n> = (* x y) definitional assertions at scope 0.
    void commit();

    // Test hook: how many monomials run() selected for sharing.
    size_t selectedCount() const { return selected_.size(); }

private:
    CoreIr& ir_;
    SortId intSort_;
    SortId realSort_;
    SortId boolSort_;

    // Per-Mul-ExprId reference count across all assertion DAGs (each ExprId
    // counted once per assertion via per-assertion visited sets, so the
    // count is "in how many distinct assertions does this Mul appear at
    // least once").
    std::unordered_map<ExprId, int> refCount_;

    // ExprId of a shared Mul -> ExprId of the fresh Variable replacing it.
    std::unordered_map<ExprId, ExprId> selected_;

    // Definitional assertions to append at commit: (= m_<n> (* x y)).
    std::vector<ExprId> defAssertions_;

    uint32_t nextAuxId_ = 0;

    // Is `e` a Mul node with >= 2 children that are NON-CONSTANT (variable
    // or another Mul)? Constants don't benefit from sharing (linearizer
    // folds them).
    bool isShareableMul(ExprId e) const;

    // Walk one assertion DAG, incrementing refCount_ for each shareable
    // Mul ExprId encountered (per-assertion visited set).
    void collectMulRefs(ExprId root);

    // Memoized DAG rewriter: replace any selected_ ExprId with its m_<n>
    // ref; rebuild ancestor nodes structurally on the way out.
    ExprId rewriteWithSubst(ExprId e,
                            std::unordered_map<ExprId, ExprId>& memo);

    // Add a fresh Variable node (Int sort by default; Real if the source
    // Mul has Real sort) and return its ExprId.
    ExprId mintShareVar(SortId sort);
};

} // namespace xolver
