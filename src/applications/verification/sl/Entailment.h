#pragma once
#include "applications/verification/sl/NativeRelations.h"
#include "applications/verification/sl/Solver.h"

namespace xolver::sl {
struct EntailmentProblem {
    // Assertions are antecedents over one shared heap. Free symbols are
    // universally quantified by refuting antecedents AND NOT conclusion.
    Request context;
    std::shared_ptr<SOMTParser::DAGNode> conclusion;
    std::vector<PredicateRelation> lemmaCandidates;
};
enum class EntailmentStatus { Valid, Invalid, Unknown, InvalidInput };
enum class EntailmentProof { Unfolding, StructuralInduction };
struct EntailmentCertificate {
    std::vector<PredicateInvariant> invariants;
    std::optional<std::size_t> unfoldingDepth;
    EntailmentProof method = EntailmentProof::Unfolding;
    std::vector<PredicateRelation> relations;
};
struct EntailmentAnswer {
    EntailmentStatus status = EntailmentStatus::Unknown;
    std::shared_ptr<const Interpretation> counterexample;
    std::optional<EntailmentCertificate> certificate;
    InductiveInference inference;
    std::string reason;
    RelationInference relations;
};
class EntailmentSolver final
    : public applications::TypedSolver<EntailmentProblem, EntailmentAnswer> {
    Limits limits_;

  public:
    explicit EntailmentSolver(Limits limits = {}) : limits_(limits) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "separation-entailment"; }
    EntailmentAnswer solve(const EntailmentProblem &) override;
};
// Candidate proofs are unconditional: query assumptions are not hypotheses of
// recursive predicate invariants. Parameters use definition node identities.
class InductiveInvariantSolver final
    : public applications::TypedSolver<Request, InductiveInference> {
    Limits limits_;

  public:
    explicit InductiveInvariantSolver(Limits limits = {}) : limits_(limits) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "separation-invariants"; }
    InductiveInference solve(const Request &) override;
};
struct RelationProblem {
    Request context;
    std::vector<PredicateRelation> candidates;
};
class RelationSolver final : public applications::TypedSolver<RelationProblem, RelationInference> {
    Limits limits_;

  public:
    explicit RelationSolver(Limits limits = {}) : limits_(limits) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "separation-predicate-relations"; }
    RelationInference solve(const RelationProblem &) override;
};
struct EntailmentCertificateProblem {
    EntailmentProblem problem;
    EntailmentCertificate certificate;
};
struct EntailmentCertificateAnswer {
    EntailmentStatus status = EntailmentStatus::Unknown;
    std::string reason;
};
class EntailmentCertificateSolver final
    : public applications::TypedSolver<EntailmentCertificateProblem, EntailmentCertificateAnswer> {
    Limits limits_;

  public:
    explicit EntailmentCertificateSolver(Limits limits = {}) : limits_(limits) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "separation-entailment-certificate"; }
    EntailmentCertificateAnswer solve(const EntailmentCertificateProblem &) override;
};
} // namespace xolver::sl
