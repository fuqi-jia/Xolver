#pragma once

#include "theory/TheorySolver.h"
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
// V1: full rebuild from activeAssignments_ on every check().
// ============================================================================
class RdlSolver : public TheorySolver {
public:
    RdlSolver();

    TheoryId id() const override { return TheoryId::RDL; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

private:
    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };
    std::vector<ActiveAssignment> activeAssignments_;

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

    std::optional<TheoryConflict> pendingConflict_;
    std::optional<TheoryLemma> pendingLemma_;

    enum class NormalizeResult { Unsupported, ImmediateConflict, Tautology, Edges, Disequality };

    NormalizeResult normalizeAndAdd(const ActiveAssignment& a);
    bool validateModel(const std::vector<RdlWeight>& dist);
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaDatabase& lemmaDb);
};

} // namespace nlcolver
