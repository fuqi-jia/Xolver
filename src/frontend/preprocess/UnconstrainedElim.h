#pragma once

#include "expr/ir.h"
#include "frontend/preprocess/ModelConverter.h"
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * UnconstrainedElim — unconstrained-value simplification (↔SAT, P1), v1.
 *
 * Conservative subset of cvc5's unconstrained-simp. Drops a top-level
 * unconditional conjunct that is a binary relational atom `(REL x t)` /
 * `(REL t x)` (REL in <, <=, >, >=, distinct; `=` is solve-eqs's job) where:
 *   - x is a numeric (Int/Real) Variable occurring EXACTLY ONCE in the whole
 *     assertion set (i.e. only in this atom), and
 *   - t is a reconstructable linear term (does not contain x, automatically).
 *
 * Soundness (↔SAT): since x appears nowhere else, the atom imposes no real
 * constraint — for any assignment to the rest of the formula, x can be chosen
 * to satisfy the atom. So dropping the atom is equisatisfiable in BOTH
 * directions. The eliminated x is reconstructed to a WITNESS satisfying the
 * atom (registerWitness on the ModelConverter): evaluate t under the final
 * model, then pick x by the relation (b, b, b+1, b-1, b+1 for >=, <=, >, <, !=).
 *
 * Guards (each a soundness requirement): single global occurrence; numeric
 * sort; x not under a UFApply/Select/Store argument (Nelson-Oppen shared term —
 * implied by the single relational-operand occurrence, but enforced); t
 * reconstructable so the witness is computable. Gated off under push/pop and
 * default-OFF via XOLVER_PP_UNCONSTRAINED_ELIM at the call site.
 */
class UnconstrainedElim {
public:
    UnconstrainedElim(CoreIr& ir, ModelConverter& mc);

    bool run();
    void commit();
    size_t eliminatedCount() const { return eliminated_; }

private:
    // Flatten top-level conjunctions; count every variable's global occurrences;
    // record variables occurring under a UFApply/Select/Store argument.
    void prepare();
    std::optional<std::string> asNumericVar(ExprId e) const;
    bool isLinearReconstructable(ExprId e) const;

    // Test whether a Variable named `name` occurs anywhere in `root`'s subtree.
    bool varOccursIn(const std::string& name, ExprId root) const;

    // Term-level unconstrained propagation (cvc5/z3 §3 / option C):
    // If `e` is an unconstrained value-term (i.e. it can take any value of
    // its sort by choice of a single occ==1 variable inside), return the
    // var name + a NEW ExprId expressing the value that variable should
    // take so that the term equals `target`. Returns nullopt otherwise.
    //
    // Handles one syntactic level on top of a Variable child:
    //   Variable v (occ==1)            → (v, target)
    //   (+ v X)  / (+ X v)             → (v, target - X)
    //   (- v X)                        → (v, target + X)
    //   (- X v)                        → (v, X - target)
    //   (- v)  (unary)                 → (v, -target)
    //   (* k v) / (* v k)  k=±1        → (v, k*target)
    //
    // Sort is restricted to Int (the LCTES target). Real follows the same
    // shape but we conservatively skip for now to avoid Mul-by-constant
    // rational-division complications.
    std::optional<std::pair<std::string, ExprId>>
        asValueUncTerm(ExprId e, ExprId target);

    // Builders for inverse-term construction (mkSub/mkNeg in the IR).
    ExprId mkSub(ExprId a, ExprId b);
    ExprId mkNeg(ExprId a);

    // Drop-action descriptor: a single witness recipe to satisfy or violate
    // an atom by choosing an unconstrained Variable's value.
    struct DropAction {
        std::string varName;
        SortId sort;
        bool useElim = false;                       // true → registerElimination, false → registerWitness
        ModelConverter::Rel rel = ModelConverter::Rel::Ge;
        ExprId bound = NullExpr;
    };

    // Find a single drop-action that makes `e` evaluate to `desiredTruth`.
    // Recurses through Not / Or (truth-preserving) and And (falsifiable).
    // Returns false if no such action is possible from this subtree.
    bool findDropAction(ExprId e, bool desiredTruth, DropAction& out) const;

    // Apply a DropAction to the ModelConverter (registerElimination /
    // registerWitness depending on .useElim).
    void applyAction(const DropAction& a);

    CoreIr& ir_;
    ModelConverter& mc_;
    SortId boolSortId_;
    SortId intSortId_;
    SortId realSortId_;

    std::vector<std::pair<ScopeLevel, ExprId>> conjuncts_;
    std::unordered_map<std::string, int> occ_;     // global occurrence count
    std::unordered_set<std::string> unsafe_;       // under UF/array argument
    std::vector<size_t> dropped_;                  // conjunct indices removed
    size_t eliminated_ = 0;
    bool didRun_ = false;
};

} // namespace xolver
