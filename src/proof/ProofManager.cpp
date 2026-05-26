#include "proof/ProofManager.h"

namespace zolver {

void ProofManager::setSatProofFile(const std::string& path) {
    satProofPath_ = path;
}

void ProofManager::recordTheoryLemma(const std::vector<SatLit>& clause,
                                      const std::string& justification) {
    theoryLemmas_.push_back({clause, justification});
}

std::string ProofManager::exportAlethe() const {
    // TODO: generate Alethe proof skeleton
    return "; Alethe proof export not yet implemented\n";
}

std::string ProofManager::exportLFSC() const {
    // TODO: generate LFSC proof skeleton
    return "; LFSC proof export not yet implemented\n";
}

} // namespace zolver
