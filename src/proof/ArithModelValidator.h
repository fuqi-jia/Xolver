#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace nlcolver {

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

    ArithModelValidator(const CoreIr& ir,
                        const NumAssignment& num,
                        const BoolAssignment& boolAsg)
        : ir_(ir), num_(num), boolAsg_(boolAsg) {}

    // Validate the given assertion roots (original-formula ExprIds).
    Verdict validate(const std::vector<ExprId>& assertions) const;

private:
    enum class Kind2 { Bool, Number, Indeterminate };
    struct TR {
        Kind2 kind = Kind2::Indeterminate;
        bool b = false;
        mpq_class n = 0;
    };

    TR eval(ExprId e) const;

    const CoreIr& ir_;
    const NumAssignment& num_;
    const BoolAssignment& boolAsg_;
};

} // namespace nlcolver
