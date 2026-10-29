#pragma once
#include "applications/verification/sl/NativeInductive.h"

namespace xolver::sl {
// A recursive conclusion uses the antecedent predicate's formal identities.
// Unlike nonrecursive invariant summaries, these properties can mention other
// inductive predicates. They are proved by simultaneous derivation induction.
using PredicateRelation = PredicateInvariant;
struct RelationInference {
    bool complete = false;
    std::vector<PredicateRelation> relations;
    std::vector<std::size_t> retained, unproved, undecided;
    std::vector<std::vector<std::shared_ptr<SOMTParser::DAGNode>>> obligations;
    std::string reason;
    uint64_t work = 0;
};
RelationInference
inferRelationsNative(const std::shared_ptr<SOMTParser::Sort> &location,
                     const std::shared_ptr<SOMTParser::Sort> &data,
                     const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                     const std::vector<InductiveDefinition> &definitions,
                     const std::vector<PredicateRelation> &candidates, Limits = {});
struct RelationalProof {
    bool proved = false;
    bool complete = false, undecided = false;
    RelationInference inference;
    std::vector<std::vector<std::shared_ptr<SOMTParser::DAGNode>>> obligations;
    std::string reason;
    uint64_t work = 0;
};
RelationalProof
proveRelationalNative(const std::shared_ptr<SOMTParser::Sort> &location,
                      const std::shared_ptr<SOMTParser::Sort> &data,
                      const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &assertions,
                      const std::shared_ptr<SOMTParser::DAGNode> &conclusion,
                      const std::vector<std::shared_ptr<SOMTParser::DAGNode>> &declarations,
                      const std::vector<InductiveDefinition> &definitions,
                      const std::vector<PredicateRelation> &candidates, Limits = {});
} // namespace xolver::sl
