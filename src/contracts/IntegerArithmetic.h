#pragma once
#include "contracts/PresburgerFormula.h"
#include <memory>
#include <optional>
#include "xolver/Result.h"
#include <cstddef>
#include <string>
#include <map>

namespace SOMTParser { class DAGNode; }

namespace xolver::pa {
struct Limits {
    std::size_t work = 2000000;
    std::size_t residues = 100000;
    std::size_t depth = 512;
};
struct Decision {
    Result result = Result::Unknown;
    std::string reason;
    std::size_t work = 0;
    std::size_t eliminated = 0;
    // Assignments to free symbols, reconstructed from the elimination trail.
    // A model is published only after all projected constraints are checked.
    // This is not a certificate of quantifier-elimination correctness.
    bool modelAvailable = false;
    std::map<std::string, std::string> model;
    std::string modelReason;
    // Present only for a completed decision when explicitly requested. These
    // equations are unverified until an independent proof kernel accepts them.
    std::optional<EliminationTrace> trace;
    std::optional<ModelEvidence> modelEvidence;
};
struct EvidenceRequest { bool elimination = false; bool model = false; };
} // namespace xolver::pa
