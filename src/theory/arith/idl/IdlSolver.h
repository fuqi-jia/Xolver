#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <string>

namespace xolver {

class TheoryAtomRegistry;

// ============================================================================
// Integer Difference Logic (IDL) solver.
// Uses difference constraint graph + Bellman-Ford negative-cycle detection.
// V1: full rebuild from the assignment trail on every check().
// ============================================================================
class IdlSolver : public ArithSolverBase {
public:
    IdlSolver();

    TheoryId id() const override { return TheoryId::IDL; }

    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;

    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

    // Model read-off from the Bellman-Ford potentials of the last consistent
    // check. A difference-logic model is determined up to a constant, so each
    // variable is anchored relative to the special __ZERO__ node:
    //   value(v) = dist[v] - dist[__ZERO__].
    // The potentials are feasible by construction, so this satisfies every
    // difference constraint. Without it the model builder defaults all IDL
    // variables to 0, which breaks the constraints (model-extraction
    // incompleteness — strict-validation flips idl_009/011/012/015).
    std::optional<TheoryModel> getModel() const override;

protected:
    void onReset() override;
    void onBacktrack(int targetLevel) override;

private:
    struct DiseqInfo {
        std::string x;
        std::string y;
        mpz_class rhs;  // x - y != rhs
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    DifferenceGraph<mpz_class> graph_;
    BellmanFord<mpz_class> bf_;
    TheoryAtomRegistry* registry_ = nullptr;

    enum class NormalizeResult { Unsupported, ImmediateConflict, Tautology, Edges, Disequality };

    NormalizeResult normalizeAndAdd(const ActiveAssignment& a);
    bool validateModel(const std::vector<mpz_class>& dist);
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaStorage& lemmaDb);

    // Potentials of the last consistent check (indexed by graph node id), used
    // by getModel(). haveModel_ is false until a check() returns Consistent.
    std::vector<mpz_class> lastDist_;
    bool haveModel_ = false;

    // Warm-start potential carried across checks. A feasible potential stays
    // feasible when constraints are removed (backtrack) and is often still
    // feasible when constraints are added, so if it satisfies every current edge
    // (an O(E) check) we SKIP the O(V·E) Bellman-Ford. The conflict/infeasible
    // path is unchanged (full BF), so this never affects soundness.
    std::vector<mpz_class> warmPot_;
};

} // namespace xolver
