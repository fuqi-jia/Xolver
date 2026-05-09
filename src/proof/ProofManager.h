#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <vector>
#include <string>
#include <memory>

namespace nlcolver {

/**
 * Proof / Certificate Manager.
 *
 * Stage J skeleton:
 *   - SAT proof tracing (DRAT/LRAT via CaDiCaL)
 *   - Theory lemma obligation tracking
 *   - NRA cell certificate export
 *   - Alethe / LFSC proof format skeleton
 */
class ProofManager {
public:
    // Enable SAT proof tracing to a file.
    void setSatProofFile(const std::string& path);

    // Record a theory lemma.
    void recordTheoryLemma(const std::vector<SatLit>& clause,
                           const std::string& justification);

    // Export proof in Alethe format (skeleton).
    std::string exportAlethe() const;

    // Export proof in LFSC format (skeleton).
    std::string exportLFSC() const;

private:
    std::string satProofPath_;
    struct LemmaRecord {
        std::vector<SatLit> clause;
        std::string justification;
    };
    std::vector<LemmaRecord> theoryLemmas_;
};

} // namespace nlcolver
