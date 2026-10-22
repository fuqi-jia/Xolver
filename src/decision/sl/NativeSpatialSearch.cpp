#include "decision/sl/NativeSpatialSearch.h"
#include "contracts/SeparationFormula.h"
#include <somtparser/ir/node.h>
#include <algorithm>
#include <functional>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <tuple>

namespace xolver::sl::detail {
namespace {
using SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
using Bound = std::optional<std::size_t>;
struct Cell { Node address, value; };
using SymbolicCells = std::vector<Cell>;
Node boolean(bool b) {
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
        b ? K::NT_CONST_TRUE : K::NT_CONST_FALSE, b ? "true" : "false");
}
Node integer(const std::string& value) {
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getInt(), K::NT_CONST, value);
}
Node makeBoolean(K k, std::vector<Node> args, bool* constructed = nullptr) {
    if (constructed) *constructed = false;
    if (k == K::NT_AND || k == K::NT_OR) {
        const bool conjunction = k == K::NT_AND;
        std::vector<Node> keep;
        for (const auto& a : args) {
            if (a->getKind() == (conjunction ? K::NT_CONST_FALSE : K::NT_CONST_TRUE))
                return boolean(!conjunction);
            if (a->getKind() != (conjunction ? K::NT_CONST_TRUE : K::NT_CONST_FALSE)) keep.push_back(a);
        }
        if (keep.empty()) return boolean(conjunction);
        if (keep.size() == 1) return keep.front();
        args = std::move(keep);
    }
    if (k == K::NT_NOT && args.size() == 1) {
        if (args[0]->getKind() == K::NT_CONST_TRUE) return boolean(false);
        if (args[0]->getKind() == K::NT_CONST_FALSE) return boolean(true);
        if (args[0]->getKind() == K::NT_NOT) return args[0]->getChild(0);
    }
    if ((k == K::NT_EQ || k == K::NT_DISTINCT) && args.size() == 2 && args[0] == args[1])
        return boolean(k == K::NT_EQ);
    if (k == K::NT_IMPLIES && args.size() == 2) {
        if (args[0]->getKind() == K::NT_CONST_FALSE || args[1]->getKind() == K::NT_CONST_TRUE || args[0] == args[1]) return boolean(true);
        if (args[0]->getKind() == K::NT_CONST_TRUE) return args[1];
        if (args[1]->getKind() == K::NT_CONST_FALSE) return makeBoolean(K::NT_NOT, {args[0]});
        if (args[0]->getKind() == K::NT_AND)
            for (auto conjunct : SOMTParser::children(args[0])) if (conjunct == args[1]) return boolean(true);
    }
    if (constructed) *constructed = true;
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
        k, SOMTParser::kindToString(k), std::move(args));
}
Node clone(const Node& n, std::vector<Node> args) {
    if (args == n->getChildren()) return n;
    return std::make_shared<SOMTParser::DAGNode>(n->getSort(), n->getKind(), n->getName(), std::move(args));
}
bool spatial(K k) {
    return k == K::NT_SEP_EMP || k == K::NT_SEP_PTO || k == K::NT_SEP_STAR || k == K::NT_SEP_WAND;
}
struct Compiler {
    Work& work;
    Node nil;
    std::set<std::string> names, auxiliaries;
    uint64_t serial = 0;
    std::unordered_map<Node, bool> spatialMemo;
    std::map<std::tuple<K, std::string, SOMTParser::Sort*, std::vector<Node>>, Node> generated;
    Node op(K k, std::vector<Node> args) {
        work.tick(args.size() + 1);
        bool constructed = false;
        auto result = makeBoolean(k, std::move(args), &constructed);
        if (!constructed) return result;
        const auto key = std::make_tuple(result->getKind(), result->getName(), result->getSort().get(), result->getChildren());
        if (result->getKind() == K::NT_VAR || result->getKind() == K::NT_QUANT_VAR) return result;
        // Only canonicalize generated Boolean operators. In particular symbol
        // identities and numeric constants are never identified by kind alone.
        if (!result->getSort()->isBool() || result->getKind() == K::NT_CONST) return result;
        auto [it, added] = generated.emplace(key, result);
        return it->second;
    }
    Node rebuilt(const Node& original, std::vector<Node> args) {
        const auto kind = original->getKind();
        if (kind == K::NT_ITE && args.size() == 3) {
            if (args[0]->getKind() == K::NT_CONST_TRUE) return args[1];
            if (args[0]->getKind() == K::NT_CONST_FALSE) return args[2];
            if (args[1] == args[2]) return args[1];
        }
        if (kind == K::NT_AND || kind == K::NT_OR || kind == K::NT_NOT ||
            kind == K::NT_IMPLIES || kind == K::NT_EQ || kind == K::NT_DISTINCT)
            return op(kind, std::move(args));
        return clone(original, std::move(args));
    }
    std::unordered_map<Node, std::pair<Bound, Bound>> bounds;
    Compiler(Work& w, const std::vector<Node>& roots, const std::vector<Node>& declarations)
        : work(w) {
        auto pending = roots;
        pending.insert(pending.end(), declarations.begin(), declarations.end());
        std::unordered_set<Node> seen;
        while (!pending.empty()) {
            work.tick(); auto n = pending.back(); pending.pop_back();
            if (!n || !seen.insert(n).second) continue;
            names.insert(n->getName());
            for (auto c : SOMTParser::children(n)) pending.push_back(c);
        }
        nil = std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getInt(),
            K::NT_SEP_NIL, "sep.nil");
    }
    Node resolve(Node n) {
        std::size_t depth = 0;
        while (n && (n->getKind() == K::NT_LET || n->getKind() == K::NT_LET_CHAIN ||
                     n->getKind() == K::NT_LET_BIND_VAR)) {
            work.tick();
            if (++depth >= work.limits.maxDepth || !n->getChildrenSize()) throw Stop("SL alias depth limit");
            n = n->getChild(n->getKind() == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0);
        }
        if (!n) throw Stop("null SL term");
        return n;
    }
    void depth(std::size_t d) { work.tick(); if (d >= work.limits.maxDepth) throw Stop("SL quantified formula depth limit"); }
    bool contains(Node n, std::size_t d = 0) {
        depth(d); n = resolve(n);
        if (auto it = spatialMemo.find(n); it != spatialMemo.end()) return it->second;
        bool result = spatial(n->getKind());
        for (auto c : SOMTParser::children(n)) result = contains(c, d + 1) || result;
        return spatialMemo.emplace(n, result).first->second;
    }
    Node fresh(bool binder = false) {
        std::string name;
        do { work.tick(); name = "@xolver.sl.heap." + std::to_string(serial++); } while (!names.insert(name).second);
        if (!binder) auxiliaries.insert(name);
        return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getInt(),
            binder ? K::NT_QUANT_VAR : K::NT_VAR, name);
    }
    SymbolicCells heap(std::size_t count, bool binder = false) {
        SymbolicCells h;
        for (std::size_t i = 0; i < count; ++i) { work.tick(); h.push_back({fresh(binder), fresh(binder)}); }
        return h;
    }
    Node valid(const SymbolicCells& h, const SymbolicCells& avoid = {}) {
        std::vector<Node> conditions;
        for (std::size_t i = 0; i < h.size(); ++i) {
            work.tick(); conditions.push_back(op(K::NT_NOT, {op(K::NT_EQ, {h[i].address, nil})}));
            for (std::size_t j = 0; j < i; ++j) {
                work.tick(); conditions.push_back(op(K::NT_NOT, {op(K::NT_EQ, {h[i].address, h[j].address})}));
            }
            for (const auto& c : avoid) {
                work.tick(); conditions.push_back(op(K::NT_NOT, {op(K::NT_EQ, {h[i].address, c.address})}));
            }
        }
        return op(K::NT_AND, std::move(conditions));
    }
    // Bounds apply to every satisfying/falsifying heap, not merely to a
    // searched representative. nullopt means no bound has been established.
    std::pair<Bound, Bound> bound(Node n, std::size_t d = 0) {
        depth(d); n = resolve(n);
        if (auto it = bounds.find(n); it != bounds.end()) return it->second;
        const auto k = n->getKind();
        std::pair<Bound, Bound> result;
        auto minimum = [](Bound a, Bound b) -> Bound { return a && b ? Bound(std::min(*a, *b)) : a ? a : b; };
        auto maximum = [](Bound a, Bound b) -> Bound { return a && b ? Bound(std::max(*a, *b)) : Bound{}; };
        if (k == K::NT_SEP_EMP) result.first = 0;
        else if (k == K::NT_SEP_PTO) result.first = 1;
        else if (k == K::NT_CONST_FALSE) result.first = 0; // vacuous bound
        else if (k == K::NT_CONST_TRUE) result.second = 0;
        else if (k == K::NT_NOT) { result = bound(n->getChild(0), d + 1); std::swap(result.first, result.second); }
        else if (k == K::NT_FORALL || k == K::NT_EXISTS) result = bound(n->getChild(0), d + 1);
        else if (k == K::NT_AND || k == K::NT_OR) {
            bool first = true;
            for (auto c : SOMTParser::children(n)) {
                auto b = bound(c, d + 1);
                if (first) { result = b; first = false; }
                else if (k == K::NT_AND) { result.first = minimum(result.first, b.first); result.second = maximum(result.second, b.second); }
                else { result.first = maximum(result.first, b.first); result.second = minimum(result.second, b.second); }
            }
        } else if (k == K::NT_SEP_STAR) {
            result.first = 0;
            for (auto c : SOMTParser::children(n)) {
                const auto b = bound(c, d + 1).first;
                if (!b || !result.first) result.first.reset();
                else if (*b > std::numeric_limits<std::size_t>::max() - *result.first) throw Stop("SL heap bound overflow");
                else *result.first += *b;
            }
        }
        return bounds.emplace(n, result).first->second;
    }
    Node substitute(Node n, const std::unordered_map<Node, Node>& map, std::size_t d = 0) {
        depth(d); n = resolve(n);
        if (auto it = map.find(n); it != map.end()) return it->second;
        std::vector<Node> args;
        for (auto c : SOMTParser::children(n)) args.push_back(substitute(c, map, d + 1));
        return rebuilt(n, std::move(args));
    }
    bool uses(const Node& n, const Node& variable, std::size_t d = 0) {
        depth(d);
        if (n == variable) return true;
        for (auto c : SOMTParser::children(n)) if (uses(c, variable, d + 1)) return true;
        return false;
    }
    Node quantify(const Node& source, Node body, std::size_t d) {
        std::vector<Node> remaining;
        for (std::size_t i = 1; i < source->getChildrenSize(); ++i) {
            auto variable = source->getChild(i);
            if (source->getKind() == K::NT_EXISTS) {
                auto terms = body->getKind() == K::NT_AND ? body->getChildren() : std::vector<Node>{body};
                Node replacement;
                for (const auto& term : terms) {
                    work.tick();
                    if (term->getKind() != K::NT_EQ || term->getChildrenSize() != 2) continue;
                    for (std::size_t side = 0; side < 2; ++side)
                        if (term->getChild(side) == variable && !uses(term->getChild(1 - side), variable, d + 1)) {
                            replacement = term->getChild(1 - side); break;
                        }
                    if (replacement) break;
                }
                if (replacement) body = substitute(body, {{variable, replacement}}, d + 1);
            }
            if (uses(body, variable, d + 1)) remaining.push_back(variable);
        }
        if (remaining.empty()) return body;
        std::vector<Node> args{body}; args.insert(args.end(), remaining.begin(), remaining.end());
        return op(source->getKind(), std::move(args));
    }
    // Exact compilation on the supplied finite heap. Quantifiers stay inside
    // their original lexical and spatial scope; a wand's extension variables
    // are universal binders, never global existential witnesses.
    Node encode(Node n, const SymbolicCells& h, std::size_t d = 0) {
        depth(d); n = resolve(n);
        if (!contains(n, d)) return n;
        const auto k = n->getKind(); const auto count = n->getChildrenSize();
        if (k == K::NT_SEP_EMP) return boolean(h.empty());
        if (k == K::NT_SEP_PTO) {
            if (count != 2) throw Stop("malformed points-to");
            if (h.size() != 1) return boolean(false);
            return op(K::NT_AND, {op(K::NT_EQ, {h[0].address, encode(n->getChild(0), h, d + 1)}),
                                  op(K::NT_EQ, {h[0].value, encode(n->getChild(1), h, d + 1)})});
        }
        if (k == K::NT_SEP_STAR) {
            if (count < 2) throw Stop("malformed separating conjunction");
            std::vector<SymbolicCells> pieces(count);
            std::vector<Node> alternatives;
            std::function<void(std::size_t)> split = [&](std::size_t i) {
                work.tick();
                if (i == h.size()) {
                    std::vector<Node> terms;
                    for (std::size_t j = 0; j < count; ++j) terms.push_back(encode(n->getChild(j), pieces[j], d + 1));
                    alternatives.push_back(op(K::NT_AND, std::move(terms))); return;
                }
                for (auto& piece : pieces) { piece.push_back(h[i]); split(i + 1); piece.pop_back(); }
            };
            split(0); return op(K::NT_OR, std::move(alternatives));
        }
        if (k == K::NT_SEP_WAND) {
            if (count != 2) throw Stop("malformed magic wand");
            auto maximum = bound(n->getChild(0), d + 1).first;
            if (!maximum) throw Stop("SL exact heap translation needs an antecedent cardinality bound");
            std::vector<Node> sizes;
            for (std::size_t size = 0;; ++size) {
                work.tick(); auto extension = heap(size, true);
                auto combined = h; combined.insert(combined.end(), extension.begin(), extension.end());
                auto premise = op(K::NT_AND, {valid(extension, h), encode(n->getChild(0), extension, d + 1)});
                auto body = op(K::NT_IMPLIES, {premise, encode(n->getChild(1), combined, d + 1)});
                if (!extension.empty()) {
                    std::vector<Node> args{body};
                    for (const auto& c : extension) { args.push_back(c.address); args.push_back(c.value); }
                    body = op(K::NT_FORALL, std::move(args));
                }
                sizes.push_back(body); if (size == *maximum) break;
            }
            return op(K::NT_AND, std::move(sizes));
        }
        if (k == K::NT_FORALL || k == K::NT_EXISTS) {
            if (count < 2) throw Stop("malformed spatial quantifier");
            std::vector<Node> args{encode(n->getChild(0), h, d + 1)};
            for (std::size_t i = 1; i < count; ++i) {
                auto variable = n->getChild(i); auto sort = variable->getSort();
                if (variable->getKind() != K::NT_QUANT_VAR || !sort || (!sort->isBool() && !sort->isInt()))
                    throw Stop("SL quantified heap arithmetic requires Int/Bool binders");
                args.push_back(variable);
            }
            return quantify(n, args[0], d + 1);
        }
        if (k == K::NT_FUNC_REC_APPLY || k == K::NT_FUNC_REC)
            throw Stop("SL recursive predicates require an explicit definition environment and fixed-point semantics");
        // Spatial terms may occur in Boolean ite/equality and arithmetic ite.
        // Recursive traversal preserves the original non-spatial operator sort.
        std::vector<Node> args;
        for (auto c : SOMTParser::children(n)) args.push_back(encode(c, h, d + 1));
        return rebuilt(n, std::move(args));
    }
    // Every satisfying heap of n must equal the returned cells (for the
    // same free-variable valuation). This is a necessary heap constraint,
    // not a syntactic guess or a finite-model cutoff. Other conjuncts are
    // still checked by encode on that heap.
    std::optional<SymbolicCells> assertedHeap(Node n, std::size_t d = 0) {
        depth(d); n = resolve(n);
        const auto kind = n->getKind();
        if (kind == K::NT_SEP_EMP) return SymbolicCells{};
        if (kind == K::NT_SEP_PTO) {
            if (n->getChildrenSize() != 2) throw Stop("malformed points-to");
            if (contains(n->getChild(0), d + 1) || contains(n->getChild(1), d + 1)) return {};
            return SymbolicCells{{n->getChild(0), n->getChild(1)}};
        }
        if (kind == K::NT_AND) {
            for (auto child : SOMTParser::children(n))
                if (auto cells = assertedHeap(child, d + 1)) return cells;
        }
        if (kind == K::NT_SEP_STAR) {
            SymbolicCells cells;
            for (auto child : SOMTParser::children(n)) {
                auto part = assertedHeap(child, d + 1);
                if (!part) return {};
                work.tick(part->size()); cells.insert(cells.end(), part->begin(), part->end());
            }
            return cells;
        }
        return {};
    }
    Node heapAssertion(const SymbolicCells& h) {
        if (h.empty()) return op(K::NT_SEP_EMP, {});
        std::vector<Node> cells;
        for (const auto& c : h) cells.push_back(op(K::NT_SEP_PTO, {c.address, c.value}));
        return cells.size() == 1 ? cells[0] : op(K::NT_SEP_STAR, std::move(cells));
    }
    // Polarity-correct finite instantiation supplies an independent global
    // refutation route and a lower witness route even with unbounded wands.
    Node approximate(Node n, bool lower, std::size_t round, std::size_t d = 0) {
        depth(d); n = resolve(n);
        if (!contains(n, d)) return n;
        const auto k = n->getKind(); const auto count = n->getChildrenSize();
        if (k == K::NT_FORALL || k == K::NT_EXISTS) {
            if (count < 2) throw Stop("malformed spatial quantifier");
            bool allBool = true;
            for (std::size_t i = 1; i < count; ++i) {
                auto s = n->getChild(i)->getSort();
                if (!s || (!s->isBool() && !s->isInt())) throw Stop("SL quantified heap arithmetic requires Int/Bool binders");
                allBool = allBool && s->isBool();
            }
            const bool existential = k == K::NT_EXISTS;
            if (!allBool && existential != lower) return boolean(!lower);
            std::vector<Node> instances;
            std::unordered_map<Node, Node> bindings;
            std::function<void(std::size_t)> enumerate = [&](std::size_t i) {
                work.tick();
                if (i == count) {
                    instances.push_back(approximate(substitute(n->getChild(0), bindings), lower, round, d + 1)); return;
                }
                auto variable = n->getChild(i);
                if (variable->getSort()->isBool()) {
                    for (bool b : {false, true}) { bindings[variable] = boolean(b); enumerate(i + 1); }
                } else {
                    // 0, 1, -1, 2, -2, ... eventually enumerates every integer.
                    bindings[variable] = nil; enumerate(i + 1);
                    for (std::size_t j = 0; j <= round; ++j) {
                        const auto magnitude = (j + 1) / 2;
                        bindings[variable] = integer((j && !(j & 1) ? "-" : "") + std::to_string(magnitude));
                        enumerate(i + 1);
                    }
                }
                bindings.erase(variable);
            };
            enumerate(1); return op(existential ? K::NT_OR : K::NT_AND, std::move(instances));
        }
        if (k == K::NT_NOT) return op(k, {approximate(n->getChild(0), !lower, round, d + 1)});
        if (k == K::NT_IMPLIES) {
            if (count < 2) throw Stop("malformed SL implication");
            auto tail = approximate(n->getChild(count - 1), lower, round, d + 1);
            for (std::size_t i = count - 1; i-- > 0;)
                tail = op(K::NT_IMPLIES, {approximate(n->getChild(i), !lower, round, d + 1), tail});
            return tail;
        }
        if (k == K::NT_SEP_WAND) return op(k, {approximate(n->getChild(0), !lower, round, d + 1),
                                                              approximate(n->getChild(1), lower, round, d + 1)});
        if (k == K::NT_AND || k == K::NT_OR || k == K::NT_SEP_STAR) {
            std::vector<Node> args;
            for (auto c : SOMTParser::children(n)) args.push_back(approximate(c, lower, round, d + 1));
            return op(k, std::move(args));
        }
        if (k == K::NT_ITE && n->getSort()->isBool()) {
            auto yes = op(K::NT_AND, {n->getChild(0), n->getChild(1)});
            auto no = op(K::NT_AND, {op(K::NT_NOT, {n->getChild(0)}), n->getChild(2)});
            return approximate(op(K::NT_OR, {yes, no}), lower, round, d + 1);
        }
        if ((k == K::NT_EQ || k == K::NT_DISTINCT || k == K::NT_XOR) && count && n->getChild(0)->getSort()->isBool()) {
            auto equivalence = [&](const Node& a, const Node& b) {
                return op(K::NT_OR, {op(K::NT_AND, {a, b}), op(K::NT_AND, {op(K::NT_NOT, {a}), op(K::NT_NOT, {b})})});
            };
            if (k == K::NT_XOR) {
                auto value = boolean(false);
                for (auto c : SOMTParser::children(n)) value = op(K::NT_NOT, {equivalence(value, c)});
                return approximate(value, lower, round, d + 1);
            }
            std::vector<Node> terms;
            for (std::size_t i = 0; i < count; ++i)
                for (std::size_t j = i + 1; j < (k == K::NT_EQ ? std::min(count, i + 2) : count); ++j) {
                    auto eq = equivalence(n->getChild(i), n->getChild(j));
                    terms.push_back(k == K::NT_EQ ? eq : op(K::NT_NOT, {eq}));
                }
            return approximate(op(K::NT_AND, std::move(terms)), lower, round, d + 1);
        }
        // A spatial Boolean used as arithmetic data is non-monotone. Replacing
        // its enclosing atom by false/true is sound until exact heap encoding.
        for (auto c : SOMTParser::children(n)) if (contains(c, d + 1)) return boolean(!lower);
        return n;
    }
};
} // namespace

bool hasSpatialBinders(const std::vector<Node>& roots) {
    Work work{{std::numeric_limits<uint64_t>::max(), 4096}};
    Compiler compiler(work, roots, {});
    auto pending = roots; std::unordered_set<Node> seen;
    while (!pending.empty()) {
        work.tick(); auto n = compiler.resolve(pending.back()); pending.pop_back();
        if (!seen.insert(n).second) continue;
        if ((n->getKind() == K::NT_FORALL || n->getKind() == K::NT_EXISTS) && compiler.contains(n)) return true;
        for (auto c : SOMTParser::children(n)) pending.push_back(c);
    }
    return false;
}

NativeDecision searchSpatialNative(const std::shared_ptr<SOMTParser::Sort>& location,
    const std::shared_ptr<SOMTParser::Sort>& data, const std::vector<Node>& assertions,
    const std::vector<Node>& declarations, Limits limits) {
    Work work{limits};
    try {
        Compiler compiler(work, assertions, declarations);
        auto root = makeBoolean(K::NT_AND, assertions);
        const auto heapBound = compiler.bound(root).first;
        const auto assertedHeap = compiler.assertedHeap(root);
        std::size_t nextHeap = 0;
        bool exact = true;
        struct Approximation {
            std::size_t round;
            uint64_t allowance = 2048;
            bool upperDone = false, lowerDone = false;
            Node upper, lower;
        };
        std::vector<Approximation> pending;
        std::size_t nextApproximation = 0;
        uint64_t heapAllowance = 2048;
        auto solve = [&](const std::vector<Node>& query, uint64_t allowance) {
            work.tick();
            Limits remaining{std::min(allowance, limits.maxSteps - work.steps), limits.maxDepth};
            auto result = decideGroundNative(location, data, query, declarations, remaining);
            work.tick(result.work);
            return result;
        };
        for (;;) {
            work.tick();
            pending.push_back({nextApproximation++});
            // Diagonal schedule: every phase introduces a new finite instance
            // set and increases the finite allowance of every unresolved old
            // set. A hard old set cannot prevent newer sets from being tried.
            for (auto& task : pending) {
                work.tick();
                if (!task.upperDone) {
                    if (!task.upper) task.upper = compiler.approximate(root, false, task.round);
                    auto above = solve({task.upper}, task.allowance);
                    if (above.result == Result::Unsat) { above.work = work.steps; return above; }
                    task.upperDone = above.result != Result::Unknown;
                }
                if (!task.lowerDone) {
                    if (!task.lower) task.lower = compiler.approximate(root, true, task.round);
                    auto below = solve({task.lower}, task.allowance);
                    if (below.result == Result::Sat) { below.work = work.steps; return below; }
                    task.lowerDone = below.result != Result::Unknown;
                }
                task.allowance = task.allowance > limits.maxSteps / 2 ? limits.maxSteps : task.allowance * 2;
            }
            work.tick(pending.size());
            pending.erase(std::remove_if(pending.begin(), pending.end(), [](const auto& task) {
                return task.upperDone && task.lowerDone;
            }), pending.end());
            // A second search preserves *all* source quantifiers on a symbolic
            // finite heap; this can establish positive forall witnesses that
            // finite instantiation alone cannot establish.
            if (exact) {
                auto h = assertedHeap ? *assertedHeap : compiler.heap(nextHeap);
                Node encoded;
                try { encoded = compiler.encode(root, h); }
                catch (const Stop& e) {
                    if (std::string(e.what()) != "SL exact heap translation needs an antecedent cardinality bound") throw;
                    exact = false;
                }
                if (exact) {
                    auto answer = solve({compiler.heapAssertion(h), compiler.valid(h), encoded}, heapAllowance);
                    if (answer.result == Result::Sat) {
                        // Auxiliary heap symbols are evidence-local. Keep their
                        // internal PA bindings, but do not export them as input declarations.
                        auto model = std::make_shared<Interpretation>(*answer.model);
                        for (const auto& name : compiler.auxiliaries) {
                            model->assignments.erase(name); model->bindings.erase(name);
                            if (model->arithmetic) model->arithmetic->publicSymbols.erase(name);
                        }
                        answer.model = std::move(model); answer.work = work.steps; return answer;
                    }
                    if (answer.result == Result::Unknown) {
                        // Other paths may solve an input outside this PA encoding.
                    } else {
                    // A positive asserted heap already covers every possible
                    // model of root, with its symbolic free values preserved.
                    if (assertedHeap || (heapBound && nextHeap == *heapBound)) return {Result::Unsat, {}, {}, work.steps};
                    ++nextHeap;
                    }
                }
            }
            heapAllowance = heapAllowance > limits.maxSteps / 2 ? limits.maxSteps : heapAllowance * 2;
        }
    } catch (const std::exception& e) { return {Result::Unknown, e.what(), {}, work.steps}; }
}

Node fixedHeapFormula(const Node& input, const HeapModel& model, Limits limits) {
    Work work{limits}; Compiler compiler(work, {input}, {});
    compiler.nil = integer(model.nil);
    SymbolicCells h;
    for (const auto& [address, value] : model.cells) { work.tick(); h.push_back({integer(address), integer(value)}); }
    return compiler.encode(input, h);
}
} // namespace xolver::sl::detail
