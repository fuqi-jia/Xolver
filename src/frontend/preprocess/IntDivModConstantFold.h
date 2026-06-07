#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * IntDivModConstantFold (Capability 8e' of the close-all-known-fails plan).
 *
 * Constant-folding pass for integer div/mod under SMT-LIB integer-division
 * semantics. Runs BEFORE IntDivModLowerer (Cap 8e) so that constant-divisor /
 * constant-dividend cases are reduced to literal `ConstInt`s without
 * introducing fresh quotient/remainder variables.
 *
 * Rewrites (only when both operands are constant integers with `b != 0`):
 *
 *   (div a b)  -->  ConstInt (a div_T b)
 *   (mod a b)  -->  ConstInt (a mod_T b)
 *
 * where `q = div_T(a, b)` and `r = mod_T(a, b)` are the SMT-LIB integer
 * quotient/remainder satisfying `a = b*q + r` with `0 <= r < |b|`.
 *
 * Cases with non-constant operand or `b = 0` are left untouched and are
 * picked up by Cap 8e (IntDivModLowerer) which introduces the standard
 * fresh-variable definitional axioms.
 *
 * Pure constant folding; never adds assertions, never strengthens the
 * formula. Memoized walk; new ExprIds, never mutates.
 */
class IntDivModConstantFold {
public:
    explicit IntDivModConstantFold(CoreIr& ir);

    bool run();
    void commit();

    bool didFold() const { return didFold_; }

private:
    ExprId foldRec(ExprId e);
    ExprId tryFoldDivMod(ExprId node);

    // Symbolic-modulus simplification of `(mod p M)` for a NON-constant modulus
    // M (e.g. M = pow2(k) in the bit-width-independent Zohar benchmarks). Layers:
    //   - distribute p into monomials, drop every monomial divisible by M
    //     (`(a*M + b) mod M -> b mod M`), drop `0` additive terms;
    //   - idempotence: a lone `(mod a M)` term collapses (`(mod (mod a M) M)`);
    //   - ITE-LIFT + MOD-OVER-ITE: an additive `(ite C a b)` term is pulled out,
    //     so `(mod (ctx + (ite C a b)) M) -> (ite C (mod (ctx+a) M) (mod (ctx+b) M))`,
    //     each branch recursively simplified, identical branches collapsed. This
    //     reaches the mods nested inside intmodtotal's `ite(M=0,..)` wrapper.
    // SOUND for ANY M (dropped t=M*s is ≡0 mod M, 0 for M=0; mod-over-ite is an
    // identity). General — no example-specific constants. `depth` caps blowup.
    ExprId trySymbolicModSimplify(ExprId e, int depth = 0);
    ExprId distribute(ExprId e);
    ExprId simplifyMul(const std::vector<ExprId>& factors);
    void collectAddSub(ExprId e, bool neg,
                       std::vector<std::pair<ExprId, bool>>& out) const;
    bool termHasFactor(ExprId t, ExprId M) const;
    ExprId rebuildAddSub(const std::vector<std::pair<ExprId, bool>>& terms);
    ExprId mkAddN(const std::vector<ExprId>& ts);
    ExprId mkMul2(ExprId a, ExprId b);
    ExprId mkMod2(ExprId a, ExprId M);
    ExprId mkIte3(ExprId c, ExprId a, ExprId b);

    // Structural hash-cons for nodes THIS pass builds. CoreIr::add does not
    // dedup (it appends), so two independently-rebuilt-but-identical arguments
    // (e.g. `-x` reconstructed on both sides of a goal) would get distinct
    // ExprIds and never compare equal. Routing the pass's own constructors
    // through this cache makes them collapse, which is what lets the
    // symbolic-modular rewrite produce a SINGLE canonical `(mod (-x) M)` that
    // both sides share. Keyed by (kind, sort, children, payload).
    ExprId cons(CoreExpr e);
    std::unordered_map<std::string, ExprId> consCache_;

    ExprId mkConstInt(int64_t v);

    CoreIr& ir_;
    SortId intSortId_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<std::pair<ScopeLevel, ExprId>> folded_;
    bool didFold_ = false;
};

} // namespace xolver
