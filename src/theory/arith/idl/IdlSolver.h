#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <string>

namespace nlcolver {

class TheoryAtomRegistry;

// ============================================================================
// Integer Difference Logic (IDL) solver.
// Uses difference constraint graph + Bellman-Ford negative-cycle detection.
// V1: full rebuild from activeAssignments_ on every check().
// ============================================================================
class IdlSolver : public TheorySolver {
public:
    IdlSolver();

    TheoryId id() const override { return TheoryId::IDL; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;
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
        mpz_class rhs;  // x - y != rhs
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    DifferenceGraph<mpz_class> graph_;
    BellmanFord<mpz_class> bf_;
    TheoryAtomRegistry* registry_ = nullptr;

    std::optional<TheoryConflict> pendingConflict_;
    std::optional<TheoryLemma> pendingLemma_;

    enum class NormalizeResult { Unsupported, ImmediateConflict, Tautology, Edges, Disequality };

    NormalizeResult normalizeAndAdd(const ActiveAssignment& a);
    bool validateModel(const std::vector<mpz_class>& dist);
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaDatabase& lemmaDb);
};

} // namespace nlcolver
