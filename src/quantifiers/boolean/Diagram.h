#pragma once
#include "quantifiers/Resources.h"
#include <cstdint>
#include <map>
#include <tuple>
#include <vector>
#include <gmpxx.h>

namespace xolver::quantifiers::boolean {
// Reduced ordered BDDs. IDs 0 and 1 denote false and true; variables are ordered
// by allocation. Nodes own child IDs, so sharing never borrows vector elements.
class Diagram {
public:
    using Id = std::uint32_t;
    using Variable = std::uint32_t;
    static constexpr Id False = 0, True = 1;
    enum class Op { And, Or, Xor };
    explicit Diagram(Resources& resources);
    Id variable();
    Variable variableOf(Id id) const;
    Id apply(Op op, Id a, Id b);
    Id negate(Id a) { return apply(Op::Xor, a, True); }
    Id conjunction(Id a, Id b) { return apply(Op::And, a, b); }
    Id disjunction(Id a, Id b) { return apply(Op::Or, a, b); }
    Id exclusiveOr(Id a, Id b) { return apply(Op::Xor, a, b); }
    Id ite(Id condition, Id yes, Id no);
    Id eliminate(Id root, const std::vector<Variable>& variables, bool universal);
    std::vector<bool> witness(Id root) const;
    bool evaluate(Id root, const std::vector<bool>& values) const;
    mpz_class count(Id root, std::vector<Variable> variables);
    std::size_t size() const { return nodes_.size(); }
    Resources& resources;
private:
    struct Node { Variable variable; Id low, high; };
    std::vector<Node> nodes_;
    Variable nextVariable_ = 0;
    std::map<std::tuple<Variable, Id, Id>, Id> unique_;
    std::map<std::tuple<Op, Id, Id>, Id> computed_;
    Id make(Variable variable, Id low, Id high);
};
}
