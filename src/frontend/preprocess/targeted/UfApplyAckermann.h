#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * UfApplyAckermann — Ackermannize scalar uninterpreted-function applications.
 *
 * TARGETED preprocessing (gated XOLVER_TARGETED_PP_UFACK, default-OFF), aimed at
 * the QF_UFNRA "hidden nonlinearity" family (Sledgehammer FFT translations): a
 * nonlinear/division term sits ONLY inside the argument of an uninterpreted
 * function, e.g. `(f3 (/ (* 2 f4) (f5 f6)))`, while the actual (un)satisfiability
 * is a trivial arithmetic fact over the UF RESULT (`x = 0 ∧ |x| = 1` -> unsat).
 * The EUF+NRA combination still routes the irrelevant division to the nonlinear
 * solver and stalls.
 *
 * Rewrite (the classic Ackermann reduction for uninterpreted functions): replace
 * each distinct application `f(a1..an)` by a fresh variable of f's return sort,
 * and for each pair of applications of the SAME f add the functional-congruence
 * axiom `(=> (and (= ai aj) ...) (= vi vj))` (skip pairs with a provably-distinct
 * constant argument). The (possibly nonlinear) arguments then survive only inside
 * those congruence equalities — and for a function applied once they vanish
 * entirely — so the formula drops from QF_UFNRA/UFNIA to QF_NRA/NIA, often to
 * pure LRA/LIA.
 *
 * Soundness: with valid congruence axioms the reduction is equisatisfiable; with
 * ANY subset of them it is still a RELAXATION (every original model induces an
 * abstract one), so abstract-UNSAT => original-UNSAT regardless. This pass adds
 * the full pairwise congruence, so it is exact. The UNSAT direction needs no
 * model reconstruction. The SAT direction would require a UF model
 * reconstruction (funcInterp) the validator-against-original cannot get from the
 * fresh vars, so a SAT result over the abstracted formula simply floors to
 * Unknown (no spurious sat) — this pass is therefore an UNSAT lever.
 *
 * Self-guarding: only fires when there is at least one scalar UF application;
 * bottom-up memoized DAG walk; fresh vars + nodes via the IR hash-cons.
 */
class UfApplyAckermann {
public:
    explicit UfApplyAckermann(CoreIr& ir);

    bool run();          // returns didRewrite()
    void commit();
    bool didRewrite() const { return didRewrite_; }
    size_t appsAbstracted() const { return appVar_.size(); }
    size_t congruences() const { return extra_.size(); }

private:
    CoreIr& ir_;
    bool didRewrite_ = false;

    std::unordered_map<ExprId, ExprId> memo_;
    std::unordered_set<ExprId> inProgress_;
    std::vector<std::pair<int, ExprId>> rewritten_;
    std::vector<ExprId> extra_;

    // Application key: (function name, rewritten argument ExprIds).
    struct AppKey {
        std::string fn;
        std::vector<ExprId> args;
        bool operator==(const AppKey& o) const { return fn == o.fn && args == o.args; }
    };
    struct AppKeyHash {
        std::size_t operator()(const AppKey& k) const {
            std::size_t h = std::hash<std::string>{}(k.fn);
            for (ExprId e : k.args)
                h ^= std::hash<uint32_t>{}(e) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<AppKey, ExprId, AppKeyHash> appVar_;
    // Per function name, the list of (args, freshVar) for pairwise congruence.
    std::unordered_map<std::string, std::vector<std::pair<std::vector<ExprId>, ExprId>>> byFn_;

    bool isScalarSort(SortId s) const;       // Int or Real
    bool intConstVal(ExprId e, mpz_class& out) const;
    ExprId rewriteRec(ExprId e);
    void buildCongruences();
};

} // namespace xolver
