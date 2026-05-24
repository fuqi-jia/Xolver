#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <string>
#include <unordered_map>

namespace nlcolver {

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

protected:
    void onReset() override;

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
};

} // namespace nlcolver
