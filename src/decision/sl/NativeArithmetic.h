#pragma once
#include "contracts/SeparationFormula.h"
#include "contracts/SeparationModel.h"
#include "decision/pa/Presburger.h"
#include <functional>
#include <memory>
#include <unordered_map>

namespace SOMTParser { class DAGNode; }
namespace xolver::sl::detail {
// Owns only native derived constraints and theory-specific bindings. Original
// arithmetic DAG nodes are reused; sep.nil is replaced by one free Int symbol.
class NativeArithmetic {
    using Node = std::shared_ptr<SOMTParser::DAGNode>;
    Work& work;
    std::set<std::string> names;
    uint64_t nextName = 0;
    Node nil;
    std::unordered_map<Node, Node> rewritten;
    std::map<std::string, Node> symbols;
    std::map<Location, Node> terms, tests, integers, predicates;
    std::vector<Node> constraints;
    Node fresh(bool boolean);
    Node pure(Node, std::size_t depth = 0);
    Node fieldTerm(const Field&) const;
    void prepare(const Prepared&, bool guard);
    pa::Decision decide();
    void reject(const Prepared&, const std::map<Location, uint64_t>&);
public:
    bool required = false;
    NativeArithmetic(Work&, const std::vector<Node>& roots, const std::vector<Node>& declarations = {});
    void integer(Location id, const Node& n) { terms.try_emplace(id, n); }
    void predicate(Location id, const Node& n) { tests.emplace(id, n); }
    Outcome solve(const Prepared&, Interpretation&);
    // Evaluate terms/predicates with all source variables and nil pinned to an
    // existing interpretation. No spatial assertion is imposed on that model.
    std::map<Location, uint64_t> evaluate(const Prepared&, const Interpretation&,
        const std::function<uint64_t(const std::string&)>& concrete);
};
} // namespace xolver::sl::detail
