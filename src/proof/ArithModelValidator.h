#pragma once

#include "expr/ir.h"
#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <map>
#include <unordered_map>
#include <vector>

namespace zolver {

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

    // Validate the given assertion roots (original-formula ExprIds).
    Verdict validate(const std::vector<ExprId>& assertions) const;

    // Evaluate one expression to a rational under the model, if fully
    // determined (else nullopt). Public wrapper over the internal evaluator,
    // used by the partial-function (div/mod-by-zero) model builder.
    std::optional<mpq_class> evalNumber(ExprId e) const;

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
        mpq_class n = 0;
        std::string tok;     // Token kind
        ArrVal arr;          // Array kind
    };

    TR eval(ExprId e) const;

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
};

} // namespace zolver
