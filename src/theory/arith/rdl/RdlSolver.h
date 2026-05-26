#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <string>
#include <unordered_map>

namespace zolver {

class TheoryAtomRegistry;

// ============================================================================
// Real Difference Logic (RDL) solver.
// Uses difference constraint graph + Bellman-Ford with infinitesimal delta.
// V1: full rebuild from the assignment trail on every check().
// ============================================================================
class RdlSolver : public ArithSolverBase {
public:
    RdlSolver();

    TheoryId id() const override { return TheoryId::RDL; }

    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;

    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

    // Model read-off: buildRdlModel already instantiates the infinitesimal δ to
    // a concrete ε and returns a full rational assignment (anchored at
    // __ZERO__=0). check() computes it for the disequality split; we keep it for
    // getModel() so the printed model satisfies every difference constraint.
    // Without it the model builder defaults all RDL variables to 0
    // (model-extraction incompleteness — strict-validation flips rdl_007/009/012).
    std::optional<TheoryModel> getModel() const override;

protected:
    void onReset() override;
    void onBacktrack(int targetLevel) override;

private:
    struct DiseqInfo {
        std::string x;
        std::string y;
        mpq_class rhs;  // x - y != rhs
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    DifferenceGraph<RdlWeight> graph_;
    BellmanFord<RdlWeight> bf_;
    TheoryAtomRegistry* registry_ = nullptr;

    enum class NormalizeResult { Unsupported, ImmediateConflict, Tautology, Edges, Disequality };

    NormalizeResult normalizeAndAdd(const ActiveAssignment& a);
    bool validateModel(const std::vector<RdlWeight>& dist);
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaStorage& lemmaDb);

    // Concrete rational model of the last consistent check (name -> value,
    // includes __ZERO__=0), used by getModel(). Valid only while haveModel_.
    std::unordered_map<std::string, mpq_class> lastModel_;
    bool haveModel_ = false;
};

} // namespace zolver
