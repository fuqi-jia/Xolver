#include "applications/sv/sl/NativeRelations.h"
#include "applications/sv/sl/InductiveExpansion.h"
#include <numeric>

namespace xolver::sl {
namespace {
using namespace detail::inductive;
// Relations are used as induction hypotheses ONLY after the antecedent
// definition has been unfolded. Generated conclusions are never rewritten in
// that pass. The final query uses only the independently closed relation set.
struct Proof {
    Unfold &unfold;
    std::shared_ptr<SOMTParser::Sort> location, data;
    std::vector<Node> symbols;
    std::vector<std::vector<Node>> obligations;
    bool undecided = false;
    std::unordered_map<Node, Node> closedRelations;
    Proof(Unfold &u, std::shared_ptr<SOMTParser::Sort> l, std::shared_ptr<SOMTParser::Sort> d,
          std::vector<Node> declarations)
        : unfold(u), location(std::move(l)), data(std::move(d)), symbols(std::move(declarations)) {}
    void validate(Node n, std::size_t depth = 0) {
        unfold.depth(depth);
        n = unfold.resolve(n);
        if (!n->getSort())
            throw detail::Stop("untyped inductive proof term");
        auto k = n->getKind();
        auto size = n->getChildrenSize();
        if (k == K::NT_FUNC_REC_APPLY) {
            unfold.definition(n);
            if (!n->getSort()->isBool())
                throw detail::Stop("inductive predicate application must be Boolean");
            for (std::size_t i = 1; i < size; ++i)
                validate(n->getChild(i), depth + 1);
            return;
        }
        if (k == K::NT_FUNC_REC)
            throw detail::Stop("bare inductive declaration is not a formula");
        if ((k == K::NT_NOT && size != 1) ||
            ((k == K::NT_SEP_WAND || k == K::NT_SEP_PTO) && size != 2) ||
            ((k == K::NT_SEP_EMP || k == K::NT_SEP_NIL) && size != 0))
            throw detail::Stop("malformed inductive proof connective");
        if (k == K::NT_AND || k == K::NT_OR || k == K::NT_NOT || k == K::NT_SEP_STAR ||
            k == K::NT_SEP_WAND)
            for (auto child : SOMTParser::children(n))
                if (!child || !child->getSort() || !child->getSort()->isBool())
                    throw detail::Stop("inductive proof connective requires Boolean children");
        for (auto child : SOMTParser::children(n))
            validate(child, depth + 1);
    }
    bool equal(Node a, Node b, std::unordered_map<Node, Node> bound = {}, std::size_t d = 0) {
        unfold.depth(d);
        a = unfold.resolve(a);
        b = unfold.resolve(b);
        if (auto it = bound.find(a); it != bound.end())
            return it->second == b;
        if (a == b)
            return true;
        auto k = a->getKind();
        if (k != b->getKind() || *a->getSort() != *b->getSort() ||
            a->getChildrenSize() != b->getChildrenSize())
            return false;
        if (k == K::NT_VAR || k == K::NT_QUANT_VAR || k == K::NT_FUNC_PARAM || k == K::NT_FUNC_REC)
            return false; // Free and recursive symbol identity is immutable.
        if (k == K::NT_FORALL || k == K::NT_EXISTS) {
            for (std::size_t i = 1; i < a->getChildrenSize(); ++i) {
                if (*a->getChild(i)->getSort() != *b->getChild(i)->getSort())
                    return false;
                bound[a->getChild(i)] = b->getChild(i);
            }
            return equal(a->getChild(0), b->getChild(0), std::move(bound), d + 1);
        }
        if (a->getName() != b->getName())
            return false;
        for (std::size_t i = 0; i < a->getChildrenSize(); ++i)
            if (!equal(a->getChild(i), b->getChild(i), bound, d + 1))
                return false;
        return true;
    }
    bool leaf(std::vector<Node> query) {
        unfold.work.tick();
        auto answer = decideNative(
            location, data, query, symbols,
            {unfold.work.limits.maxSteps - unfold.work.steps, unfold.work.limits.maxDepth});
        unfold.work.tick(answer.work);
        if (answer.result == Result::Unsat) {
            obligations.push_back(std::move(query));
            return true;
        }
        undecided = undecided || answer.result == Result::Unknown;
        return false;
    }
    std::vector<Node> flatten(Node n, K kind, std::size_t d = 0) {
        unfold.depth(d);
        n = unfold.resolve(n);
        if (n->getKind() != kind)
            return {n};
        std::vector<Node> result;
        for (auto child : SOMTParser::children(n)) {
            auto terms = flatten(child, kind, d + 1);
            result.insert(result.end(), terms.begin(), terms.end());
        }
        return result;
    }
    Node transform(Node n, const std::unordered_map<Node, Node> &relations, bool expand,
                   bool positive = true, std::size_t d = 0) {
        unfold.depth(d);
        n = unfold.resolve(n);
        auto k = n->getKind();
        if (k == K::NT_FUNC_REC_APPLY) {
            const auto &definition = unfold.definition(n);
            if (expand)
                return unfold.instantiate(n, definition.body);
            auto it = relations.find(definition.symbol);
            return positive && it != relations.end() ? unfold.instantiate(n, it->second) : n;
        }
        if (k == K::NT_FUNC_REC || !n->getChildrenSize())
            return n;
        // Unknown-variance contexts cannot weaken their recursive subterms.
        if (!expand && k != K::NT_AND && k != K::NT_OR && k != K::NT_NOT && k != K::NT_SEP_STAR &&
            k != K::NT_SEP_WAND && k != K::NT_IMPLIES && k != K::NT_FORALL && k != K::NT_EXISTS &&
            k != K::NT_ITE)
            return n;
        auto children = n->getChildren();
        for (std::size_t i = 0; i < children.size(); ++i) {
            if (((k == K::NT_FORALL || k == K::NT_EXISTS) && i) ||
                (!expand && k == K::NT_ITE && i == 0))
                continue;
            auto polarity = k == K::NT_NOT || ((k == K::NT_IMPLIES || k == K::NT_SEP_WAND) &&
                                               i + 1 != children.size())
                                ? !positive
                                : positive;
            children[i] = transform(children[i], relations, expand, polarity, d + 1);
        }
        return unfold.rebuild(n, std::move(children));
    }
    bool prove(Node a, Node b, std::vector<Node> context = {}, std::size_t d = 0) {
        unfold.depth(d);
        a = unfold.resolve(a);
        b = unfold.resolve(b);
        if (equal(a, b) || a->getKind() == K::NT_CONST_FALSE || b->getKind() == K::NT_CONST_TRUE)
            return true;
        if (!unfold.recursive(a) && !unfold.recursive(b)) {
            context.push_back(a);
            context.push_back(operation(K::NT_NOT, {b}));
            return leaf(std::move(context));
        }
        if (!unfold.heapDependent(a) && a->getKind() != K::NT_CONST_TRUE) {
            context.push_back(a);
            if (leaf(context))
                return true;
            return prove(truth(true), b, context, d + 1);
        }
        if (!unfold.heapDependent(b)) {
            auto query = context;
            query.push_back(operation(K::NT_NOT, {b}));
            if (leaf(std::move(query)))
                return true;
        }
        auto ak = a->getKind(), bk = b->getKind();
        if (bk == K::NT_IMPLIES && b->getChildrenSize() >= 2) {
            std::vector<Node> assumptions{a};
            for (std::size_t i = 0; i + 1 < b->getChildrenSize(); ++i)
                assumptions.push_back(b->getChild(i));
            return prove(operation(K::NT_AND, std::move(assumptions)),
                         b->getChild(b->getChildrenSize() - 1), context, d + 1);
        }
        if (ak == K::NT_IMPLIES && a->getChildrenSize() >= 2) {
            std::vector<Node> disjuncts;
            for (std::size_t i = 0; i + 1 < a->getChildrenSize(); ++i)
                disjuncts.push_back(operation(K::NT_NOT, {a->getChild(i)}));
            disjuncts.push_back(a->getChild(a->getChildrenSize() - 1));
            return prove(operation(K::NT_OR, std::move(disjuncts)), b, context, d + 1);
        }
        if (ak == K::NT_OR) {
            for (auto n : SOMTParser::children(a))
                if (!prove(n, b, context, d + 1))
                    return false;
            return true;
        }
        if (bk == K::NT_AND) {
            for (auto n : SOMTParser::children(b))
                if (!prove(a, n, context, d + 1))
                    return false;
            return true;
        }
        if (ak == K::NT_AND) {
            std::vector<Node> spatial;
            for (auto n : flatten(a, K::NT_AND))
                if (unfold.heapDependent(n))
                    spatial.push_back(n);
                else
                    context.push_back(n);
            if (!context.empty() && leaf(context))
                return true;
            if (spatial.size() <= 1)
                return prove(operation(K::NT_AND, spatial), b, context, d + 1);
            if (bk == K::NT_OR) {
                for (auto n : SOMTParser::children(b))
                    if (prove(operation(K::NT_AND, spatial), n, context, d + 1))
                        return true;
                return false;
            }
            for (auto n : spatial)
                if (prove(n, b, context, d + 1))
                    return true;
            return false;
        }
        if (bk == K::NT_OR) {
            for (auto n : SOMTParser::children(b))
                if (prove(a, n, context, d + 1))
                    return true;
            return false;
        }
        if ((ak == K::NT_EXISTS || ak == K::NT_FORALL) && ak == bk &&
            a->getChildrenSize() == b->getChildrenSize()) {
            std::unordered_map<Node, Node> left, right;
            for (std::size_t i = 1; i < a->getChildrenSize(); ++i) {
                if (*a->getChild(i)->getSort() != *b->getChild(i)->getSort())
                    return false;
                auto variable = unfold.fresh(a->getChild(i), true);
                symbols.push_back(variable);
                left[a->getChild(i)] = variable;
                right[b->getChild(i)] = variable;
            }
            return prove(unfold.substitute(a->getChild(0), left),
                         unfold.substitute(b->getChild(0), right), context, d + 1);
        }
        if (ak == K::NT_EXISTS || bk == K::NT_FORALL) {
            auto quantified = ak == K::NT_EXISTS ? a : b;
            std::unordered_map<Node, Node> bindings;
            for (std::size_t i = 1; i < quantified->getChildrenSize(); ++i) {
                auto variable = unfold.fresh(quantified->getChild(i), true);
                bindings[quantified->getChild(i)] = variable;
                symbols.push_back(variable);
            }
            auto opened = unfold.substitute(quantified->getChild(0), bindings);
            return ak == K::NT_EXISTS ? prove(opened, b, context, d + 1)
                                      : prove(a, opened, context, d + 1);
        }
        if (ak == K::NT_FUNC_REC_APPLY && bk == K::NT_FUNC_REC_APPLY &&
            a->getChild(0) == b->getChild(0)) {
            for (std::size_t i = 1; i < a->getChildrenSize(); ++i) {
                auto x = a->getChild(i), y = b->getChild(i);
                if (equal(x, y))
                    continue;
                if (unfold.heapDependent(x) || unfold.heapDependent(y))
                    return false;
                auto query = context;
                query.push_back(operation(K::NT_NOT, {operation(K::NT_EQ, {x, y})}));
                if (!leaf(query))
                    return false;
            }
            return true;
        }
        if (ak == K::NT_SEP_STAR || bk == K::NT_SEP_STAR) {
            auto left = flatten(a, K::NT_SEP_STAR), right = flatten(b, K::NT_SEP_STAR);
            auto empty = [](Node n) { return n->getKind() == K::NT_SEP_EMP; };
            std::erase_if(left, empty);
            std::erase_if(right, empty);
            if (left.size() != right.size())
                return false;
            std::vector<bool> used(right.size());
            auto match = [&](auto &&self, std::size_t i) -> bool {
                unfold.depth(d + i);
                if (i == left.size())
                    return true;
                for (std::size_t j = 0; j < right.size(); ++j)
                    if (!used[j] && prove(left[i], right[j], context, d + 1)) {
                        used[j] = true;
                        if (self(self, i + 1))
                            return true;
                        used[j] = false;
                    }
                return false;
            };
            return match(match, 0);
        }
        if (ak == K::NT_NOT && bk == K::NT_NOT)
            return prove(transform(b->getChild(0), closedRelations, false), a->getChild(0), context,
                         d + 1);
        if (ak == K::NT_SEP_WAND && bk == K::NT_SEP_WAND)
            return prove(transform(b->getChild(0), closedRelations, false), a->getChild(0), context,
                         d + 1) &&
                   prove(a->getChild(1), b->getChild(1), context, d + 1);
        return false;
    }
};
std::unordered_map<Node, Node> hypotheses(const std::vector<PredicateRelation> &candidates,
                                          const std::vector<std::size_t> &retained) {
    std::unordered_map<Node, std::vector<Node>> groups;
    for (auto i : retained)
        groups[candidates[i].predicate].push_back(candidates[i].property);
    std::unordered_map<Node, Node> result;
    for (auto &[p, properties] : groups)
        result[p] = operation(K::NT_AND, std::move(properties));
    return result;
}
RelationInference infer(Proof &proof, const std::vector<PredicateRelation> &candidates) {
    auto &u = proof.unfold;
    RelationInference answer;
    for (const auto &[symbol, definition] : u.definitions)
        proof.validate(definition->body);
    for (std::size_t i = 0; i < candidates.size(); ++i) {
        const auto &c = candidates[i];
        if (!u.definitions.contains(c.predicate) || !c.property || !c.property->getSort() ||
            !c.property->getSort()->isBool())
            throw detail::Stop("invalid inductive relation");
        u.collect({c.property});
        const auto &def = *u.definitions.at(c.predicate);
        u.scope(c.property, {def.parameters.begin(), def.parameters.end()});
        proof.validate(c.property);
        answer.retained.push_back(i);
    }
    for (;;) {
        auto rules = hypotheses(candidates, answer.retained);
        std::vector<std::size_t> remaining;
        proof.obligations.clear();
        for (auto i : answer.retained) {
            const auto &c = candidates[i];
            const auto &def = *u.definitions.at(c.predicate);
            std::unordered_map<Node, Node> formals;
            for (auto n : def.parameters) {
                auto fresh = u.fresh(n, true);
                formals[n] = fresh;
                proof.symbols.push_back(fresh);
            }
            // Strict descendants of this unfolded antecedent may use IHs.
            auto left = proof.transform(u.substitute(def.body, formals), rules, false);
            auto right = proof.transform(u.substitute(c.property, formals), {}, true);
            const bool previousUnknown = proof.undecided;
            proof.undecided = false;
            if (proof.prove(left, right))
                remaining.push_back(i);
            else {
                answer.unproved.push_back(i);
                if (proof.undecided)
                    answer.undecided.push_back(i);
            }
            proof.undecided = proof.undecided || previousUnknown;
        }
        if (remaining == answer.retained)
            break;
        answer.retained = std::move(remaining);
    }
    for (auto i : answer.retained)
        answer.relations.push_back(candidates[i]);
    answer.obligations = proof.obligations;
    answer.work = u.work.steps;
    answer.complete = true;
    if (!answer.unproved.empty())
        answer.reason = "relations without a closed structural derivation discarded";
    return answer;
}
} // namespace
RelationInference inferRelationsNative(const std::shared_ptr<SOMTParser::Sort> &location,
                                       const std::shared_ptr<SOMTParser::Sort> &data,
                                       const std::vector<Node> &declarations,
                                       const std::vector<InductiveDefinition> &definitions,
                                       const std::vector<PredicateRelation> &candidates,
                                       Limits limits) {
    detail::Work work{limits};
    RelationInference answer;
    try {
        heapSorts(location, data);
        Unfold u{work};
        prepare(u, {}, declarations, definitions);
        Proof proof{u, location, data, declarations};
        return infer(proof, candidates);
    } catch (const std::exception &e) {
        answer.reason = e.what();
        answer.work = work.steps;
    }
    return answer;
}
RelationalProof proveRelationalNative(const std::shared_ptr<SOMTParser::Sort> &location,
                                      const std::shared_ptr<SOMTParser::Sort> &data,
                                      const std::vector<Node> &assertions, const Node &conclusion,
                                      const std::vector<Node> &declarations,
                                      const std::vector<InductiveDefinition> &definitions,
                                      const std::vector<PredicateRelation> &candidates,
                                      Limits limits) {
    detail::Work work{limits};
    RelationalProof answer;
    try {
        heapSorts(location, data);
        Unfold u{work};
        auto roots = assertions;
        roots.push_back(conclusion);
        prepare(u, roots, declarations, definitions);
        Proof proof{u, location, data, declarations};
        for (auto n : roots)
            proof.validate(n);
        answer.inference = infer(proof, candidates);
        auto rules = hypotheses(candidates, answer.inference.retained);
        proof.closedRelations = rules;
        auto left = proof.transform(operation(K::NT_AND, assertions), rules, false);
        answer.proved = proof.prove(left, conclusion);
        answer.complete = true;
        answer.undecided = proof.undecided;
        answer.obligations = std::move(proof.obligations);
        answer.reason = answer.proved ? "" : "structural entailment derivation remains open";
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    answer.work = work.steps;
    return answer;
}
} // namespace xolver::sl
