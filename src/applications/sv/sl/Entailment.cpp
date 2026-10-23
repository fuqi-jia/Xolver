#include "applications/sv/sl/Entailment.h"
#include "applications/sv/sl/InductiveExpansion.h"
#include "contracts/SeparationFormula.h"
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
enum class Proposal { Unconditional, Conditional };
std::vector<PredicateRelation>
relationCandidates(const EntailmentProblem &p, detail::Work &work, Proposal stage,
                   const std::vector<PredicateRelation> &proved = {}) {
    work.tick(p.lemmaCandidates.size());
    auto result = p.lemmaCandidates;
    detail::inductive::Unfold expansion{work};
    detail::inductive::prepare(expansion, {}, p.context.declarations, p.context.definitions);
    std::set<std::pair<Node, Node>> requested;
    if (stage == Proposal::Conditional) {
        auto calls = [&](const std::vector<Node> &roots) {
            std::set<std::pair<Node, bool>> found;
            std::vector<std::pair<Node, bool>> pending;
            for (auto n : roots)
                pending.emplace_back(n, true);
            while (!pending.empty()) {
                work.tick();
                auto [n, positive] = pending.back();
                pending.pop_back();
                n = expansion.resolve(n);
                auto k = n->getKind();
                if (k == K::NT_FUNC_REC_APPLY) {
                    found.emplace(expansion.definition(n).symbol, positive);
                    continue;
                }
                if (k == K::NT_FUNC_REC)
                    continue;
                for (std::size_t i = 0; i < n->getChildrenSize(); ++i) {
                    if ((k == K::NT_FORALL || k == K::NT_EXISTS) && i)
                        continue;
                    auto polarity =
                        k == K::NT_NOT || ((k == K::NT_IMPLIES || k == K::NT_SEP_WAND) &&
                                           i + 1 != n->getChildrenSize())
                            ? !positive
                            : positive;
                    pending.emplace_back(n->getChild(i), polarity);
                    if (k == K::NT_ITE && !i)
                        pending.emplace_back(n->getChild(i), !polarity);
                }
            }
            return found;
        };
        for (auto [a, sign] : calls(p.context.assertions))
            for (auto [b, rightSign] : calls({p.conclusion}))
                if (sign == rightSign)
                    requested.emplace(sign ? a : b, sign ? b : a);
    }
    // Same-position signatures propose relations; proof closure determines
    // which ones hold. Clients can supply arbitrary parameter maps explicitly.
    for (const auto &left : p.context.definitions)
        for (const auto &right : p.context.definitions) {
            work.tick();
            if (!left.symbol || !right.symbol)
                continue;
            if (left.symbol == right.symbol || left.parameters.size() != right.parameters.size())
                continue;
            bool compatible = true;
            for (std::size_t i = 0; i < left.parameters.size(); ++i)
                compatible = compatible && left.parameters[i] && right.parameters[i] &&
                             left.parameters[i]->getSort() && right.parameters[i]->getSort() &&
                             *left.parameters[i]->getSort() == *right.parameters[i]->getSort();
            if (!compatible)
                continue;
            work.tick(left.parameters.size() + 1);
            std::vector<Node> arguments{right.symbol};
            arguments.insert(arguments.end(), left.parameters.begin(), left.parameters.end());
            auto conclusion = std::make_shared<SOMTParser::DAGNode>(
                SOMTParser::SortManager::getBool(), K::NT_FUNC_REC_APPLY, right.symbol->getName(),
                std::move(arguments));
            result.push_back({left.symbol, conclusion});
            if (stage == Proposal::Unconditional ||
                !requested.contains({left.symbol, right.symbol}))
                continue;
            bool alreadyProved = false;
            for (const auto &lemma : proved) {
                auto rhs = lemma.property;
                if (lemma.predicate != left.symbol || !rhs ||
                    rhs->getKind() != K::NT_FUNC_REC_APPLY ||
                    rhs->getChildrenSize() != left.parameters.size() + 1 ||
                    rhs->getChild(0) != right.symbol)
                    continue;
                bool sameArguments = true;
                for (std::size_t i = 0; i < left.parameters.size(); ++i)
                    sameArguments = sameArguments && rhs->getChild(i + 1) == left.parameters[i];
                alreadyProved = alreadyProved || sameArguments;
            }
            if (alreadyProved)
                continue;
            std::set<std::string> seen;
            for (const auto *origin : {&left, &right}) {
                std::unordered_map<Node, Node> substitutions;
                for (std::size_t i = 0; i < origin->parameters.size(); ++i)
                    substitutions[origin->parameters[i]] = left.parameters[i];
                std::vector<Node> pending{origin->body};
                while (!pending.empty()) {
                    work.tick();
                    auto term = expansion.resolve(pending.back());
                    pending.pop_back();
                    auto kind = term->getKind();
                    if (kind == K::NT_FUNC_REC || kind == K::NT_FUNC_REC_APPLY)
                        continue;
                    if (term->getSort() && term->getSort()->isBool() && kind != K::NT_CONST_TRUE &&
                        kind != K::NT_CONST_FALSE && !expansion.heapDependent(term)) {
                        auto guard = expansion.substitute(term, substitutions);
                        if (guard->getKind() == K::NT_CONST_TRUE ||
                            guard->getKind() == K::NT_CONST_FALSE)
                            continue;
                        std::vector<Node> guards{guard};
                        if (guard->getKind() == kind && (kind == K::NT_GT || kind == K::NT_LT))
                            guards.push_back(detail::inductive::operation(
                                kind == K::NT_GT ? K::NT_GE : K::NT_LE, guard->getChildren()));
                        const auto count = guards.size();
                        for (std::size_t i = 0; i < count; ++i)
                            guards.push_back(detail::inductive::operation(K::NT_NOT, {guards[i]}));
                        for (auto g : guards) {
                            const auto text = SOMTParser::dumpSMTLIB2(g);
                            work.tick(text.size() + 1);
                            if (seen.insert(text).second)
                                result.push_back(
                                    {left.symbol,
                                     detail::inductive::operation(K::NT_IMPLIES, {g, conclusion})});
                        }
                    }
                    // Bound variables cannot escape into a guard template.
                    if (kind != K::NT_FORALL && kind != K::NT_EXISTS)
                        for (auto child : SOMTParser::children(term))
                            pending.push_back(child);
                }
            }
        }
    return result;
}
} // namespace
RelationInference RelationSolver::solve(const RelationProblem &problem) {
    if (problem.context.recursion != RecursiveSemantics::LeastFixedPoint) {
        RelationInference answer;
        answer.reason = "predicate relations require explicit least-fixed-point semantics";
        return answer;
    }
    const auto &c = problem.context;
    return inferRelationsNative(c.location, c.data, c.declarations, c.definitions,
                                problem.candidates, limits_);
}
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
            detail::Work work{limits_};
            auto proposed = relationCandidates(p, work, Proposal::Unconditional);
            auto relational =
                proveRelationalNative(p.context.location, p.context.data, p.context.assertions,
                                      p.conclusion, p.context.declarations, p.context.definitions,
                                      proposed, {limits_.maxSteps - work.steps, limits_.maxDepth});
            work.tick(relational.work);
            if (!relational.proved && work.steps < limits_.maxSteps) {
                auto conditional = relationCandidates(p, work, Proposal::Conditional,
                                                      relational.inference.relations);
                if (conditional.size() > proposed.size()) {
                    relational = proveRelationalNative(
                        p.context.location, p.context.data, p.context.assertions, p.conclusion,
                        p.context.declarations, p.context.definitions, conditional,
                        {limits_.maxSteps - work.steps, limits_.maxDepth});
                    work.tick(relational.work);
                }
            }
            answer.relations = std::move(relational.inference);
            if (relational.proved) {
                answer.status = EntailmentStatus::Valid;
                certificate.method = EntailmentProof::StructuralInduction;
                certificate.relations = answer.relations.relations;
                answer.certificate = std::move(certificate);
                return answer;
            }
            if (work.steps >= limits_.maxSteps) {
                answer.reason =
                    relational.reason.empty() ? "SL work budget exhausted" : relational.reason;
                return answer;
            }
            const Limits remaining{limits_.maxSteps - work.steps, limits_.maxDepth};
            auto candidates = p.context.invariantCandidates;
            // An inductive false summary proves an unproductive recursive cycle
            // empty; it is checked by the same rule as every other candidate.
            for (const auto &definition : p.context.definitions)
                candidates.push_back({definition.symbol, std::make_shared<SOMTParser::DAGNode>(
                                                             SOMTParser::SortManager::getBool(),
                                                             K::NT_CONST_FALSE, "false")});
            auto solved = solveInductiveNative(p.context.location, p.context.data, query,
                                               p.context.declarations, p.context.definitions,
                                               candidates, remaining);
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
        if (p.certificate.method == EntailmentProof::StructuralInduction) {
            if (context.recursion != RecursiveSemantics::LeastFixedPoint ||
                context.definitions.empty() || p.certificate.unfoldingDepth ||
                !p.certificate.invariants.empty())
                throw std::invalid_argument("malformed structural induction certificate");
            auto proof = proveRelationalNative(
                context.location, context.data, context.assertions, p.problem.conclusion,
                context.declarations, context.definitions, p.certificate.relations, limits_);
            if (!proof.complete || !proof.inference.complete) {
                answer.reason = proof.reason;
                return answer;
            }
            const bool allProved =
                proof.inference.retained.size() == p.certificate.relations.size();
            if (!proof.proved && proof.undecided) {
                answer.reason = "certificate entailment has an inconclusive proof premise";
                return answer;
            }
            if (!allProved && !proof.inference.undecided.empty()) {
                answer.reason = "certificate relation has an inconclusive proof premise";
                return answer;
            }
            answer.status =
                allProved && proof.proved ? EntailmentStatus::Valid : EntailmentStatus::Invalid;
            answer.reason =
                allProved ? proof.reason : "certificate contains an unproved predicate relation";
            return answer;
        }
        if (p.certificate.method != EntailmentProof::Unfolding || !p.certificate.relations.empty())
            throw std::invalid_argument("unknown or inconsistent entailment certificate method");
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
