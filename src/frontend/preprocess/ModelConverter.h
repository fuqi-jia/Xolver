#pragma once

#include "expr/ir.h"
#include "util/RealValue.h"
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * ModelConverter — reconstructs variables eliminated by ↔SAT preprocessing
 * passes (solve-eqs / Gaussian linear variable elimination).
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
 * Linear-only: solve-eqs eliminates from linear equalities, so t is a linear
 * arithmetic term and the evaluator handles Add/Sub/Neg/Mul-by-const/ToReal/
 * Variable/constants over rationals. A variable whose model value is not
 * rational (e.g. an algebraic NRA value) leaves the dependent eliminated var
 * unreconstructed (reconstruct() returns false), which the caller treats as a
 * model it cannot vouch for.
 */
class ModelConverter {
public:
    // Record that `name` (sort `sort`) was eliminated and equals the value of
    // `definingExpr`. Replayed in reverse registration order.
    void registerElimination(std::string name, SortId sort, ExprId definingExpr);

    bool empty() const { return elims_.empty(); }
    size_t size() const { return elims_.size(); }

    // Reconstruct every eliminated variable into the model, evaluating its
    // defining term under the current assignment, newest elimination first.
    // Writes BOTH channels the solver reads: `numAsg` (typed RealValue) and
    // `strAsg` (the legacy string map that Solver::modelMatchesOriginal and
    // dumpModel consume, in bare mpq form e.g. "5" / "3/2"). Returns true iff
    // every eliminated variable was reconstructed; false if some defining term
    // could not be evaluated (model left without that variable).
    bool reconstruct(std::unordered_map<std::string, RealValue>& numAsg,
                     std::unordered_map<std::string, std::string>& strAsg,
                     const CoreIr& ir) const;

private:
    struct Elim {
        std::string name;
        SortId sort;
        ExprId expr;
    };
    std::vector<Elim> elims_;

    // Iterative post-order evaluation of a linear arithmetic term over the
    // rational environment `env` (name -> value). nullopt if a leaf variable is
    // missing or a node is not linear-arithmetic-evaluable.
    static std::optional<mpq_class> evalRational(
        ExprId root, const CoreIr& ir,
        const std::unordered_map<std::string, mpq_class>& env);
};

} // namespace xolver
