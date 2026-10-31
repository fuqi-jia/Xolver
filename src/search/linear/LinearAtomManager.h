#pragma once

#include "algebra/linear/LinearExpr.h"
#include "contracts/TheorySolver.h"
#include "search/lra/GeneralSimplex.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <string>
#include <optional>

namespace xolver {

/**
 * LinearAtomManager: solver-local helper for linear constraint management.
 *
 * Bound to a single GeneralSimplex instance. Handles:
 *   - TermExpr -> LinearForm extraction (pure function, no state)
 *   - LinearFormKey canonicalization -> GeneralSimplex aux var
 *   - Relation -> bound assertion
 *   - Conflict translation
 *
 * Does NOT create SAT literals. Does NOT interact with Atomizer.
 * All dynamic atom registration (SAT var creation) is handled by TheoryAtomRegistry.
 */
class LinearAtomManager {
public:
    LinearAtomManager() = default;

    // -------------------------------------------------------------------------
    // TermExpr -> LinearForm extraction (delegates to free functions in LinearExpr.h)
    // -------------------------------------------------------------------------
    bool extractLinearConstraint(ExprId eid, const NativeTerms& ir,
                                  std::unordered_map<std::string, mpq_class>& coeffs,
                                  mpq_class& rhs, Relation& rel) const;

    // -------------------------------------------------------------------------
    // LinearFormKey -> GeneralSimplex aux var
    //
    // Semantic: creates aux such that aux = lhs - rhs, i.e. lhs = rhs + aux.
    // So aux = 0  <=>  lhs = rhs.
    // -------------------------------------------------------------------------
    int getOrCreateAuxVar(GeneralSimplex& gs,
                          const LinearFormKey& lhs,
                          const mpq_class& rhs);

    // -------------------------------------------------------------------------
    // Assert a bound on an aux var.
    // Records bound reasons for later conflict translation.
    // -------------------------------------------------------------------------
    // When integerForm is true, the aux var is integer-valued, so a strict
    // bound is tightened to the equivalent non-strict integer bound
    // (s < 0 => s <= -1, s > 0 => s >= 1). This lets the simplex prove
    // integer-empty ranges like n < d < n+1 directly, instead of leaving a
    // δ-strict bound that branch-and-bound chases forever.
    bool assertBound(GeneralSimplex& gs, int auxVar, Relation rel,
                     bool value, SatLit reasonLit, int level = 0,
                     bool integerForm = false);

    struct RelationBounds {
        std::optional<DeltaRational> lower, upper;
    };
    static RelationBounds effectiveBounds(Relation rel, bool value, bool integerForm);
    struct RelationBoundViews {
        const DeltaRational* lower = nullptr;
        const DeltaRational* upper = nullptr;
    };
    // Immutable canonical endpoints with process lifetime. The owning value
    // API above keeps its existing coordinate and strictness semantics.
    static RelationBoundViews effectiveBoundViews(Relation rel, bool value, bool integerForm);

    // -------------------------------------------------------------------------
    // Translate a GeneralSimplex conflict to a TheoryConflict.
    // -------------------------------------------------------------------------
    TheoryConflict translateConflict(const GeneralSimplex& gs) const;

    // -------------------------------------------------------------------------
    // Var name <-> GeneralSimplex var index
    // -------------------------------------------------------------------------
    int getOrCreateVar(GeneralSimplex& gs, const std::string& name);
    std::string getVarName(int idx) const;
    // Const lookup of an already-created variable's simplex index, or -1 if
    // the name has never been registered. Does NOT create a variable.
    int findVarIndex(const std::string& name) const;

    // Interpret a linear atom at the current simplex point using exact
    // rational/infinitesimal ordering. Missing coordinates leave the hint open.
    // A point value is a backtrackable phase hint, not an entailment or verdict.
    std::optional<bool> evaluateAtModel(
        const GeneralSimplex& gs, const LinearAtomPayload& atom) const;

    // Reverse of getOrCreateAuxVar: if `aux` is an auxiliary variable created
    // for some constraint, recover its defining form (aux = Σ lhs - rhs over
    // ORIGINAL variable names). Returns false for original (non-aux) vars. Used
    // by Gomory-cut generation to re-express a cut over original variables.
    bool auxForm(int aux, LinearFormKey& lhsOut, mpq_class& rhsOut) const;

    struct AuxFormView {
        const LinearFormKey& lhs;
        const mpq_class& rhs;
    };
    // References remain valid until this manager is destroyed, including after
    // auxiliary registrations and solver backtracks. Definitions are never
    // erased or modified; callers must keep the manager alive.
    std::optional<AuxFormView> auxFormView(int aux) const;

private:
    // Canonical (lhs, rhs) -> aux var (solver-local)
    struct FormKey {
        LinearFormKey lhs;
        mpq_class rhs;
        bool operator==(const FormKey& o) const {
            return lhs == o.lhs && rhs == o.rhs;
        }
    };
    struct FormKeyView {
        const LinearFormKey& lhs;
        const mpq_class& rhs;
    };
    struct FormKeyHash {
        using is_transparent = void;
        std::size_t operator()(const FormKey& k) const {
            return (*this)(FormKeyView{k.lhs, k.rhs});
        }
        std::size_t operator()(FormKeyView k) const {
            std::size_t h = LinearFormKeyHash{}(k.lhs);
            h ^= MpqHash{}(k.rhs) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };
    struct FormKeyEqual {
        using is_transparent = void;
        bool operator()(const FormKey& a, const FormKey& b) const { return a == b; }
        bool operator()(const FormKey& a, FormKeyView b) const { return a.lhs == b.lhs && a.rhs == b.rhs; }
        bool operator()(FormKeyView a, const FormKey& b) const { return (*this)(b, a); }
    };
    std::unordered_map<FormKey, int, FormKeyHash, FormKeyEqual> formToAux_;

    // Reverse map: aux var index -> its defining (lhs, rhs).
    std::unordered_map<int, FormKey> auxToForm_;

    // Variable name -> GeneralSimplex var index
    std::unordered_map<std::string, int> varToIndex_;
    // iter-104 perf: reverse map for O(1) getVarName instead of O(N) linear
    // scan of varToIndex_. Populated synchronously with varToIndex_ at every
    // getOrCreateVar call. LIA/LRA hot loops call getVarName per simplex
    // variable when materializing conflicts and dumping models — making the
    // reverse lookup O(1) eliminates O(N²) total cost in those loops.
    std::unordered_map<int, std::string> indexToVar_;


};

} // namespace xolver
