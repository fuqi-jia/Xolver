#pragma once
#include "applications/verification/sl/NativeSeparation.h"

namespace xolver::sl {
// Explicit SL least-fixed-point semantics. A generic SMT define-fun-rec
// declaration is not sufficient to select this interpretation.
struct InductiveDefinition {
    std::shared_ptr<SOMTParser::DAGNode> symbol;
    std::shared_ptr<SOMTParser::DAGNode> body;
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> parameters;
};
// Properties use the matching definition's formal-parameter node identities.
// They can contain nonrecursive spatial formulas as well as arithmetic.
struct PredicateInvariant {
    std::shared_ptr<SOMTParser::DAGNode> predicate, property;
};
struct InductiveInference {
    bool complete = false;
    std::vector<PredicateInvariant> invariants;
    std::vector<std::size_t> retained, refuted, undecided;
    // Each query is F(I) AND NOT I for one retained property, with fresh formals.
    std::vector<std::vector<std::shared_ptr<SOMTParser::DAGNode>>> obligations;
    std::string reason;
    uint64_t work = 0;
};
InductiveInference
inferInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                     const std::shared_ptr<SOMTParser::Sort> &data,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                     const std::vector<InductiveDefinition> &definitions,
                     const std::vector<PredicateInvariant> &candidates, Limits = {});
struct InductiveAnswer {
    NativeDecision decision;
    InductiveInference inference;
    // UNSAT uses an upper approximation; SAT uses a lower approximation.
    std::optional<std::size_t> unfoldingDepth;
};
InductiveAnswer
solveInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                     const std::shared_ptr<SOMTParser::Sort> &data,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &assertions,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                     const std::vector<InductiveDefinition> &definitions,
                     const std::vector<PredicateInvariant> &candidates, Limits = {});
// Rebuild and decide one upper approximation after proving EVERY supplied
// invariant. UNSAT validates the certificate, SAT rejects this proof attempt.
NativeDecision
replayInductiveUnsat(const std::shared_ptr<SOMTParser::Sort> &location,
                     const std::shared_ptr<SOMTParser::Sort> &data,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &assertions,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                     const std::vector<InductiveDefinition> &definitions,
                     const std::vector<PredicateInvariant> &invariants, std::size_t depth,
                     Limits = {});
NativeDecision
decideInductiveNative(const std::shared_ptr<SOMTParser::Sort> &location,
                      const std::shared_ptr<SOMTParser::Sort> &data,
                      const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &assertions,
                      const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                      const std::vector<InductiveDefinition> &definitions, Limits = {});
} // namespace xolver::sl
