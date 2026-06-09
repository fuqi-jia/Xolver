#pragma once

#include "expr/ir.h"
#include "theory/core/TheorySolver.h"
#include "util/RealValue.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * ArithModelValidator — independent end-to-end model check.
 *
 * Re-evaluates a set of assertions (the ORIGINAL, pre-lowering formula)
 * under a concrete numeric/boolean assignment, using its own arithmetic
 * evaluator. It is deliberately INDEPENDENT of the theory solvers' and
 * CandidateModelSearch's evaluators: defense-in-depth requires that the
 * validator not share code with whatever produced the model, so a bug in
 * the producer cannot be masked by the same bug in the checker.
 *
 * Verdict semantics (conservative on purpose):
 *   - Satisfied     : every assertion evaluates to true under the model.
 *   - Violated      : some assertion evaluates DEFINITELY to false (all of
 *                     its variables are present and it is fully evaluable).
 *   - Indeterminate : at least one assertion could not be fully evaluated
 *                     (a missing variable, an uninterpreted function, or an
 *                     unsupported construct) and none was definitely false.
 *
 * Callers must only act on `Violated` (e.g. downgrade Sat → Unknown).
 * `Indeterminate` must be treated as "cannot disprove" — never as a
 * violation — so the validator can only reject genuinely-wrong models and
 * never spuriously rejects a correct one.
 */
class ArithModelValidator {
public:
    enum class Verdict { Satisfied, Violated, Indeterminate };

    using NumAssignment = std::unordered_map<std::string, mpq_class>;
    using BoolAssignment = std::unordered_map<std::string, bool>;
    using ArrayAssignment =
        std::unordered_map<std::string, TheorySolver::TheoryModel::ArrayInterp>;

    ArithModelValidator(const CoreIr& ir,
                        const NumAssignment& num,
                        const BoolAssignment& boolAsg)
        : ir_(ir), num_(num), boolAsg_(boolAsg) {}

    using TokenAssignment = std::unordered_map<std::string, std::string>;

    // Array-aware constructor (QF_AX). The array interps map each array
    // variable name to a (default, override-list) interpretation; index/
    // element values are opaque tokens compared by equality. `tok` carries
    // scalar (index/element) variable -> opaque token assignments.
    ArithModelValidator(const CoreIr& ir,
                        const NumAssignment& num,
                        const BoolAssignment& boolAsg,
                        const ArrayAssignment& arr,
                        const TokenAssignment& tok)
        : ir_(ir), num_(num), boolAsg_(boolAsg), arr_(&arr), tok_(&tok) {}

    using FuncInterpMap =
        std::unordered_map<std::string, TheorySolver::TheoryModel::FuncInterp>;

    // Provide interpretations for uninterpreted functions so UFApply nodes can
    // be evaluated by table lookup (else they are Indeterminate). Optional;
    // when unset, UF applications remain unevaluable. The pointer must outlive
    // this validator.
    void setFunctionInterps(const FuncInterpMap* fi) { funcInterps_ = fi; }

    using RealAssignment = std::unordered_map<std::string, RealValue>;
    // Provide EXACT real-algebraic values (e.g. √2) for variables, from the
    // theory's typed model channel (numericAssignments). Consulted before the
    // rational `num_` map, so NRA/NIRA algebraic witnesses validate instead of
    // being Indeterminate. Optional; pointer must outlive this validator.
    void setRealAssignments(const RealAssignment* ra) { real_ = ra; }

    // Provide TYPED values for array-read terms, keyed by
    // (array-operand ExprId, index value). Used by the combination model check
    // to surface the arith value the theory assigned to a purifier-bridged array
    // read `(= v (select A i))` — which EUF's array-model export does not carry —
    // so a `(mod (select A i) M)` witness validates instead of reading a stale
    // array default. Keying on the ARRAY-OPERAND node (not the whole select)
    // plus the evaluated index is robust to purification rebuilding the select
    // when its index is compound, and to NESTED reads `(select (select m b) i)`
    // (the inner `(select m b)` operand keeps its ExprId). The value travels as a
    // RealValue (no string token), consulted before the array-interpretation
    // path. Optional; pointer must outlive this validator.
    using SelectOverrideMap = std::map<std::pair<ExprId, mpq_class>, RealValue>;
    void setSelectOverride(const SelectOverrideMap* so) { selOverride_ = so; }

    // Datatype-SELECTOR value override (DT+arith combination model check). The
    // Purifier bridges an arith-valued datatype selector `(fst p)` into a fresh
    // shared scalar via `(= v (fst p))` (routed to EUF); the arith theory assigns
    // v a value but the DT model export does not reflect it, so the validator
    // cannot evaluate `(fst p)` and floors a genuine sat to Unknown. This maps the
    // (hash-consed) selector ExprId directly to its typed value. Optional; pointer
    // must outlive this validator. Sound: the bridge equality holds in the model,
    // and every ORIGINAL assertion is still independently re-checked.
    using SelectorOverrideMap = std::unordered_map<ExprId, RealValue>;
    void setSelectorOverride(const SelectorOverrideMap* so) { selectorOverride_ = so; }

    // Free read-only array variables eliminated by ReadOnlyArrayElim's
    // write-array mode (XOLVER_TARGETED_PP). Such a var W is never stored to and
    // appears only in reads (Ackermannized) and in array (dis)equalities `(= S W)`.
    // Because W is unconstrained except at finitely many read indices, it can
    // always be chosen UNEQUAL to S (differ at an unread index), so any equality
    // involving W evaluates to false here. SOUND for the SAT direction (the found
    // model extends to a real one with W != S) — and ReadOnlyArrayElim suppresses
    // UNSAT to Unknown whenever this mode fired, so it cannot cause a wrong UNSAT.
    // Keyed on the (hash-cons-stable) Variable ExprId. Optional; outlives this.
    void setFreeArrayVars(const std::unordered_set<ExprId>* fv) { freeArrayVars_ = fv; }

    // When ON, a `(select a i)` over an Int/Real-element array surfaces a concrete
    // numeric/bool element as a TYPED value (so enclosing arithmetic mod/div/+ can
    // consume it) instead of an opaque element token. Gated because it also makes
    // the validator able to DEFINITELY evaluate nested store/select reads, which
    // can expose that a theory-produced array model is wrong (e.g. a self-store
    // case whose model never validated but escaped as sat while the read was
    // Indeterminate). Off by default → default verdict path unchanged. Set ON by
    // the array-read bridge model-completion path (XOLVER_COMB_ARRAY_BRIDGE_MODEL).
    void setNumericArrayElements(bool b) { numElems_ = b; }

    // Validate the given assertion roots (original-formula ExprIds).
    Verdict validate(const std::vector<ExprId>& assertions) const;

    // Evaluate one expression to a rational under the model, if fully
    // determined (else nullopt). Public wrapper over the internal evaluator,
    // used by the partial-function (div/mod-by-zero) model builder.
    std::optional<mpq_class> evalNumber(ExprId e) const;

    // XOLVER_PP_VALIDATOR_MEMO: memoize eval over ExprId. eval is a pure
    // function of (ExprId, fixed model), so on a shared-subterm (DAG) formula
    // the un-memoized recursion re-evaluates shared nodes exponentially; the
    // cache makes validation linear in the DAG. Transparent — identical
    // verdicts, only faster. Off by default (it can shift floor timing, so the
    // master A/Bs it before default-on).
    void setEvalMemo(bool on) { memoEnabled_ = on; }

private:
    // Array value: a default element token plus an ordered set of overrides.
    // A std::map keeps later stores overriding earlier ones deterministically.
    struct ArrVal {
        std::string deflt;
        std::map<std::string, std::string> overrides;  // index-token -> elem-token
    };

    enum class Kind2 { Bool, Number, Token, Array, Indeterminate };
    struct TR {
        Kind2 kind = Kind2::Indeterminate;
        bool b = false;
        RealValue n;         // Number kind — RealValue subsumes rational AND
                             // real-algebraic (e.g. √2), so NRA/NIRA algebraic
                             // witnesses are evaluable, not just rationals.
        std::string tok;     // Token kind
        ArrVal arr;          // Array kind
    };

    TR eval(ExprId e) const;       // cached dispatcher (memo when enabled)
    TR evalImpl(ExprId e) const;   // the actual evaluator (recurses via eval)
    // Iterative bottom-up pre-pass: fills `cache` with every subterm's TR so the
    // recursive eval/evalImpl resolves children from it and never recurses deeply
    // (deep-formula/term stack-overflow guard). Used by validate()/evalNumber().
    void warmEval(ExprId root, std::unordered_map<ExprId, TR>& cache) const;

    // Coerce a fully-evaluated TR into an opaque equality token (Number/Bool/
    // Token). Returns nullopt if not coercible (e.g. Array or Indeterminate).
    std::optional<std::string> asToken(const TR& r) const;

    const CoreIr& ir_;
    // Held BY VALUE: callers (incl. tests) may pass temporaries, and these maps
    // are small + the validator is one-shot. Avoids dangling-reference UB.
    NumAssignment num_;
    BoolAssignment boolAsg_;
    const ArrayAssignment* arr_ = nullptr;
    const TokenAssignment* tok_ = nullptr;
    const FuncInterpMap* funcInterps_ = nullptr;
    const RealAssignment* real_ = nullptr;
    const SelectOverrideMap* selOverride_ = nullptr;
    const SelectorOverrideMap* selectorOverride_ = nullptr;
    const std::unordered_set<ExprId>* freeArrayVars_ = nullptr;
    bool numElems_ = false;

    // eval memo (XOLVER_PP_VALIDATOR_MEMO). Valid for this validator's lifetime
    // (the model is fixed), keyed by original-formula ExprId.
    bool memoEnabled_ = false;
    mutable std::unordered_map<ExprId, TR> evalMemo_;
    // When non-null (set for the duration of a warmed validate()/evalNumber()),
    // eval() consults it first — lets warmEval's bottom-up fill bound recursion
    // independently of memoEnabled_. Points at a caller-local map; never dangling.
    mutable std::unordered_map<ExprId, TR>* prepassCache_ = nullptr;
};

} // namespace xolver
