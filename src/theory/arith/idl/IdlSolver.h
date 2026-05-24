#pragma once

#include "theory/arith/ArithSolverBase.h"
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
// V1: full rebuild from the assignment trail on every check().
// ============================================================================
class IdlSolver : public ArithSolverBase {
public:
    IdlSolver();

    TheoryId id() const override { return TheoryId::IDL; }

    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;

    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

protected:
    void onReset() override;

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
};

} // namespace nlcolver
