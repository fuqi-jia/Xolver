#pragma once
#include "applications/verification/sl/NativeInductive.h"
#include "contracts/SeparationFormula.h"
#include <gmpxx.h>
#include <set>
#include <somtparser/ir/node.h>
#include <unordered_map>
#include <unordered_set>

namespace xolver::sl::detail::inductive {
using SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
Node truth(bool);
Node operation(K, std::vector<Node>);
// Definition validation, capture-free instantiation and polarity-aware
// approximation shared by the SL application's inductive algorithms.
struct Unfold {
    Work &work;
    std::unordered_map<Node, const InductiveDefinition *> definitions;
    std::unordered_map<Node, Node> summaries;
    uint64_t next = 0;
    std::set<std::string> names;
    explicit Unfold(Work &budget) : work(budget) {}
    void depth(std::size_t);
    Node resolve(Node);
    Node fresh(const Node &, bool free = false);
    void collect(const std::vector<Node> &);
    static bool compatible(const Node &, const Node &);
    void scope(Node, const std::unordered_set<Node> &, std::unordered_set<Node> = {},
               std::size_t = 0);
    bool recursive(Node, std::size_t = 0);
    bool heapDependent(Node, std::size_t = 0);
    void positive(Node, bool polarity = true, std::size_t = 0);
    std::optional<mpz_class> numeral(const Node &);
    Node rebuild(const Node &, std::vector<Node>);
    Node substitute(Node, std::unordered_map<Node, Node>, std::size_t = 0);
    const InductiveDefinition &definition(Node);
    Node instantiate(Node application, Node body);
    Node formula(Node, bool lower, std::size_t fuel, std::size_t = 0);
};
void prepare(Unfold &, const std::vector<Node> &, const std::vector<Node> &,
             const std::vector<InductiveDefinition> &);
void heapSorts(const std::shared_ptr<SOMTParser::Sort> &,
               const std::shared_ptr<SOMTParser::Sort> &);
} // namespace xolver::sl::detail::inductive
