#include "applications/sv/sl/Entailment.h"
#include "ir/NativeBuilder.h"

namespace xolver::sl {
namespace {
using namespace native;
std::vector<Node> refutation(const EntailmentProblem &p) {
    if (!p.context.location || !p.context.data)
        throw std::invalid_argument("entailment requires an explicit heap signature");
    auto query = p.context.assertions;
    query.push_back(p.conclusion);
    for (auto n : query)
        if (!n || !n->getSort() || !n->getSort()->isBool())
            throw std::invalid_argument("entailment antecedents and conclusion must be Boolean");
    query.back() = std::make_shared<SOMTParser::DAGNode>(
        SOMTParser::SortManager::getBool(), K::NT_NOT, "not", std::vector<Node>{p.conclusion});
    return query;
}
EntailmentStatus validity(Result result) {
    return result == Result::Unsat ? EntailmentStatus::Valid
           : result == Result::Sat ? EntailmentStatus::Invalid
                                   : EntailmentStatus::Unknown;
}
} // namespace
InductiveInference InductiveInvariantSolver::solve(const Request &request) {
    if (request.recursion != RecursiveSemantics::LeastFixedPoint) {
        InductiveInference answer;
        answer.reason = "inductive invariants require explicit least-fixed-point semantics";
        return answer;
    }
    return inferInductiveNative(request.location, request.data, request.declarations,
                                request.definitions, request.invariantCandidates, limits_);
}
EntailmentAnswer EntailmentSolver::solve(const EntailmentProblem &p) {
    EntailmentAnswer answer;
    try {
        auto query = refutation(p);
        NativeDecision result;
        EntailmentCertificate certificate;
        if (p.context.definitions.empty()) {
            if (!p.context.invariantCandidates.empty())
                throw std::invalid_argument("invariant candidates require predicate definitions");
            result = decideNative(p.context.location, p.context.data, query, p.context.declarations,
                                  limits_);
        } else {
            if (p.context.recursion != RecursiveSemantics::LeastFixedPoint) {
                answer.reason =
                    "recursive entailment requires explicit least-fixed-point semantics";
                return answer;
            }
            auto candidates = p.context.invariantCandidates;
            // An inductive false summary proves an unproductive recursive cycle
            // empty; it is checked by the same rule as every other candidate.
            for (const auto &definition : p.context.definitions)
                candidates.push_back({definition.symbol, std::make_shared<SOMTParser::DAGNode>(
                                                             SOMTParser::SortManager::getBool(),
                                                             K::NT_CONST_FALSE, "false")});
            auto solved = solveInductiveNative(p.context.location, p.context.data, query,
                                               p.context.declarations, p.context.definitions,
                                               candidates, limits_);
            result = std::move(solved.decision);
            answer.inference = std::move(solved.inference);
            certificate.invariants = answer.inference.invariants;
            certificate.unfoldingDepth = solved.unfoldingDepth;
        }
        answer.status = validity(result.result);
        answer.reason = std::move(result.reason);
        if (answer.status == EntailmentStatus::Invalid)
            answer.counterexample = std::move(result.model);
        if (answer.status == EntailmentStatus::Valid)
            answer.certificate = std::move(certificate);
    } catch (const std::invalid_argument &e) {
        answer.status = EntailmentStatus::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
EntailmentCertificateAnswer
EntailmentCertificateSolver::solve(const EntailmentCertificateProblem &p) {
    EntailmentCertificateAnswer answer;
    try {
        auto query = refutation(p.problem);
        const auto &context = p.problem.context;
        NativeDecision result;
        if (context.definitions.empty()) {
            if (!p.certificate.invariants.empty() || p.certificate.unfoldingDepth)
                throw std::invalid_argument("recursive certificate for a nonrecursive entailment");
            result =
                decideNative(context.location, context.data, query, context.declarations, limits_);
        } else {
            if (context.recursion != RecursiveSemantics::LeastFixedPoint ||
                !p.certificate.unfoldingDepth)
                throw std::invalid_argument(
                    "recursive certificate requires LFP semantics and unfolding depth");
            result = replayInductiveUnsat(
                context.location, context.data, query, context.declarations, context.definitions,
                p.certificate.invariants, *p.certificate.unfoldingDepth, limits_);
        }
        answer.status = validity(result.result);
        answer.reason = std::move(result.reason);
    } catch (const std::invalid_argument &e) {
        answer.status = EntailmentStatus::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::sl
