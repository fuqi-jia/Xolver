#pragma once

#include "LinearExpr.h"
#include "theory/core/TheorySolver.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <string>
#include <optional>

namespace zolver {

/**
 * LinearAtomManager: solver-local helper for linear constraint management.
 *
 * Bound to a single GeneralSimplex instance. Handles:
 *   - CoreExpr -> LinearForm extraction (pure function, no state)
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
    // CoreExpr -> LinearForm extraction (delegates to free functions in LinearExpr.h)
    // -------------------------------------------------------------------------
    bool extractLinearConstraint(ExprId eid, const CoreIr& ir,
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
    bool assertBound(GeneralSimplex& gs, int auxVar, Relation rel,
                     bool value, SatLit reasonLit, int level = 0);

    // -------------------------------------------------------------------------
    // Translate a GeneralSimplex conflict to a TheoryConflict.
    // -------------------------------------------------------------------------
    TheoryConflict translateConflict(const GeneralSimplex& gs) const;

    // -------------------------------------------------------------------------
    // Var name <-> GeneralSimplex var index
    // -------------------------------------------------------------------------
    int getOrCreateVar(GeneralSimplex& gs, const std::string& name);
    std::string getVarName(int idx) const;

private:
    // Canonical (lhs, rhs) -> aux var (solver-local)
    struct FormKey {
        LinearFormKey lhs;
        mpq_class rhs;
        bool operator==(const FormKey& o) const {
            return lhs == o.lhs && rhs == o.rhs;
        }
    };
    struct FormKeyHash {
        std::size_t operator()(const FormKey& k) const {
            std::size_t h = LinearFormKeyHash{}(k.lhs);
            h ^= std::hash<std::string>{}(k.rhs.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<FormKey, int, FormKeyHash> formToAux_;

    // Variable name -> GeneralSimplex var index
    std::unordered_map<std::string, int> varToIndex_;


};

} // namespace zolver
