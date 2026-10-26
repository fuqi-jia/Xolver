#pragma once

#include "ir/NativeTerms.h"
#include "base/RealValue.h"
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * ModelConverter — reconstructs variables eliminated by ↔SAT preprocessing
 * passes (solve-eqs).
 *
 * When a pass removes a user variable `x` by substituting `x ↦ t` (t over the
 * remaining variables) and dropping the defining equality, the solver produces
 * a model over the *reduced* variable set. The eliminated variable is absent,
 * so the model does not satisfy the ORIGINAL assertions (invariant 1's
 * ModelValidator pass would fail). This class records each (x, t) and replays
 * them in REVERSE order on the final model: each x is set to the value of t
 * evaluated under the current (already partly reconstructed) assignment.
 *
 * Reverse order is required because an earlier-eliminated x's defining term t
 * may reference a variable eliminated later — that later variable is
 * reconstructed first, so its value is available when x is computed.
 *
 * Exact rational replay: the evaluator handles Add/Sub/Neg/Mul/ToReal/
 * Variable/constants over rationals. A variable whose model value is not
 * rational (e.g. an algebraic NRA value) leaves the dependent eliminated var
 * unreconstructed (reconstruct() returns false), which the caller treats as a
 * model it cannot vouch for.
 */
class ModelConverter {
public:
    // solve-eqs: `name` was eliminated and EQUALS the value of `definingExpr`.
    // STRICT semantics: every free variable in `definingExpr` must have a
    // value in the final model. Missing dep ⇒ reconstruct() returns false.
    void registerElimination(std::string name, SortId sort, ExprId definingExpr);

    bool empty() const { return steps_.empty(); }
    size_t size() const { return steps_.size(); }

    // Reconstruct every eliminated variable into the model, newest step first
    // (a step's term may reference a later-eliminated var). Writes BOTH channels
    // the solver reads: `numAsg` (typed RealValue) and `strAsg` (the legacy
    // string map Solver::modelMatchesOriginal and dumpModel consume, bare mpq
    // form e.g. "5" / "3/2"). Returns true iff every step was reconstructed.
    bool reconstruct(std::unordered_map<std::string, RealValue>& numAsg,
                     std::unordered_map<std::string, std::string>& strAsg,
                     const NativeTerms& ir) const;

private:
    struct Step {
        std::string name;
        SortId sort;
        ExprId expr;     // Defining term.
    };
    std::vector<Step> steps_;

    // Iterative post-order evaluation of an arithmetic term over the rational
    // environment `env` (name -> value). nullopt if a leaf variable is missing
    // or a node is not arithmetic-evaluable. `boolEnv` is consulted only for
    // Kind::Ite condition evaluation (callers that pass nullptr lose Ite
    // support but keep the linear core). Missing numeric variables make
    // reconstruction fail rather than inventing a value.
    static std::optional<mpq_class> evalRational(
        ExprId root, const NativeTerms& ir,
        const std::unordered_map<std::string, mpq_class>& env,
        const std::unordered_map<std::string, bool>* boolEnv = nullptr);

    // Iterative evaluation of a boolean expression over `boolEnv` (bool vars)
    // and `env` (rationals, for arithmetic relations). Missing bool vars default
    // to false (matching dumpModel's unconstrained default). nullopt if a node
    // is not evaluable (e.g. an unevaluable numeric relation operand).
    static std::optional<bool> evalBool(
        ExprId root, const NativeTerms& ir,
        const std::unordered_map<std::string, bool>& boolEnv,
        const std::unordered_map<std::string, mpq_class>& env);
};

} // namespace xolver
