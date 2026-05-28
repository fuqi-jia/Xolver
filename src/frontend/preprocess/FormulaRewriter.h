#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <cstddef>

namespace xolver {

/**
 * FormulaRewriter — a DAG-safe, memoized, fixpoint simplifier over CoreIr.
 *
 * This is the generic Xolver formula rewriter (plan.md §2, invariant 6). It is
 * the system-level "preprocessing / canonicalization" pass that the per-theory
 * stacks rely on. It is gated behind the XOLVER_PP_REWRITE env flag and is a
 * pure IR-to-IR transform: it only APPENDS CoreExpr nodes (CoreIr::add never
 * mutates), so the originalAssertions_ snapshot taken before it runs keeps
 * referencing the original formula for ModelValidator.
 *
 * Soundness contract: every rule is truth-preserving under SMT-LIB semantics.
 * (Brute-force/random-model equivalence is enforced in the unit tests.) The
 * rewriter NEVER folds partial functions (integer div/mod, real /, pow, abs);
 * those are owned by dedicated passes with the correct partial-function
 * semantics.
 *
 * Rules implemented:
 *   Boolean: not/and/or/implies/xor const-fold + identities + absorption +
 *            complementary-literal (x ∧ ¬x → ⊥, x ∨ ¬x → ⊤) + dedup + flatten.
 *   ITE:     ite(⊤,a,b)→a, ite(⊥,a,b)→b, ite(c,a,a)→a, ite(c,⊤,⊥)→c,
 *            ite(c,⊥,⊤)→¬c.
 *   Eq/Dist: reflexivity (= a a → ⊤, distinct a a → ⊥), numeric-constant eval,
 *            boolean iff identities (= x ⊤ → x, = x ⊥ → ¬x) when provably bool.
 *   Arith:   const-fold + flatten of +,−,neg,*; identities (+0, *1, *0, −0,
 *            neg neg); relational const-eval (< ≤ > ≥ over numeric constants).
 */
class FormulaRewriter {
public:
    enum class Verdict { Normal, Unsat };

    FormulaRewriter(CoreIr& ir, SortId boolSort);

    // Rewrite every current assertion. Returns Unsat iff some top-level
    // assertion simplifies to the boolean constant false (the conjunction of
    // assertions is then unsatisfiable). On Normal, commit() may be called.
    Verdict run();

    // Replace the assertion list with the rewritten assertions, dropping any
    // that simplified to the boolean constant true. Only valid after a Normal
    // run().
    void commit();

    bool changed() const { return changed_; }

    // Rewrite a single expression to its normal form (exposed for testing).
    ExprId rewrite(ExprId e);

private:
    // Structural hash-cons key for output nodes.
    struct ConsKey {
        Kind kind;
        SortId sort;
        std::vector<ExprId> children;
        Payload::Value payload;
        bool operator==(const ConsKey& o) const {
            return kind == o.kind && sort == o.sort &&
                   children == o.children && payload == o.payload;
        }
    };
    struct ConsKeyHash {
        std::size_t operator()(const ConsKey& k) const;
    };

    ExprId rewriteRec(ExprId e);
    // Simplify a node whose children are already in normal form. Loops to a
    // local fixpoint. Returns the (possibly new) ExprId.
    ExprId simplifyNode(Kind kind, SortId sort, std::vector<ExprId> children,
                        const Payload& payload);

    // --- node construction (hash-consed) ---
    ExprId mk(Kind kind, SortId sort, std::vector<ExprId> children, Payload payload);
    ExprId mkBool(bool v);
    ExprId mkIntOrReal(const mpq_class& v, SortId sort); // NullExpr if cannot represent

    // --- queries ---
    bool isTrue(ExprId e) const;
    bool isFalse(ExprId e) const;
    bool isBoolConst(ExprId e, bool& out) const;
    bool isProvablyBool(ExprId e) const;
    // Negation of an already-normal-form expr (hash-consed).
    ExprId negate(ExprId e);

    CoreIr& ir_;
    SortId boolSort_;
    SortId intSort_;
    SortId realSort_;

    std::unordered_map<ExprId, ExprId> memo_;
    std::unordered_map<ConsKey, ExprId, ConsKeyHash> cons_;
    std::vector<std::pair<ScopeLevel, ExprId>> rewritten_;
    bool changed_ = false;
    bool unsat_ = false;
};

} // namespace xolver
