#include "quantifiers/boolean/Diagram.h"
#include <algorithm>
#include <functional>
#include <set>

namespace xolver::quantifiers::boolean {
Diagram::Diagram(Resources& r) : resources(r) {
    const auto terminal = std::numeric_limits<Variable>::max();
    nodes_ = {{terminal, False, False}, {terminal, True, True}};
}
Diagram::Id Diagram::make(Variable variable, Id low, Id high) {
    resources.tick();
    if (low == high) return low;
    const auto key = std::tuple{variable, low, high};
    if (auto found = unique_.find(key); found != unique_.end()) return found->second;
    resources.nodes(nodes_.size() + 1);
    if (nodes_.size() >= std::numeric_limits<Id>::max())
        throw Exhausted("BDD node identifier space exhausted");
    const auto id = static_cast<Id>(nodes_.size());
    nodes_.push_back({variable, low, high});
    unique_.emplace(key, id);
    return id;
}
Diagram::Id Diagram::variable() {
    if (nextVariable_ == std::numeric_limits<Variable>::max())
        throw Exhausted("BDD variable identifier space exhausted");
    return make(nextVariable_++, False, True);
}
Diagram::Variable Diagram::variableOf(Id id) const { return nodes_.at(id).variable; }
Diagram::Id Diagram::apply(Op op, Id a, Id b) {
    Resources::Frame frame(resources);
    if (a > b) std::swap(a, b);
    if (a == b) return op == Op::Xor ? False : a;
    if (op == Op::And) {
        if (a == False) return False;
        if (a == True) return b;
    } else if (op == Op::Or) {
        if (a == False) return b;
        if (a == True) return True;
    } else if (a == False) return b;
    if (b <= True) return op == Op::And ? Id(a && b) :
                              op == Op::Or ? Id(a || b) : Id(a != b);
    const auto key = std::tuple{op, a, b};
    if (auto found = computed_.find(key); found != computed_.end()) return found->second;
    const Node na = nodes_.at(a), nb = nodes_.at(b);
    const Variable top = std::min(na.variable, nb.variable);
    const Id low = apply(op, na.variable == top ? na.low : a,
                            nb.variable == top ? nb.low : b);
    const Id high = apply(op, na.variable == top ? na.high : a,
                             nb.variable == top ? nb.high : b);
    const Id result = make(top, low, high);
    // The cache is an optimization; its size does not determine semantics.
    if (resources.limits.nodes && computed_.size() >= resources.limits.nodes)
        computed_.clear();
    computed_.emplace(key, result);
    return result;
}
Diagram::Id Diagram::ite(Id c, Id yes, Id no) {
    if (yes == no) return yes;
    if (c == True) return yes;
    if (c == False) return no;
    return disjunction(conjunction(c, yes), conjunction(negate(c), no));
}
Diagram::Id Diagram::eliminate(Id root, const std::vector<Variable>& variables, bool universal) {
    const std::set<Variable> quantified(variables.begin(), variables.end());
    std::map<Id, Id> memo;
    std::function<Id(Id)> visit = [&](Id id) -> Id {
        Resources::Frame frame(resources);
        if (id <= True) return id;
        if (auto found = memo.find(id); found != memo.end()) return found->second;
        const Node node = nodes_.at(id);
        const auto low = visit(node.low), high = visit(node.high);
        const auto result = quantified.contains(node.variable)
            ? apply(universal ? Op::And : Op::Or, low, high)
            : make(node.variable, low, high);
        memo.emplace(id, result);
        return result;
    };
    return visit(root);
}
std::vector<bool> Diagram::witness(Id root) const {
    if (root == False) throw std::logic_error("false BDD has no witness");
    std::vector<bool> values(nextVariable_, false);
    while (root > True) {
        const auto node = nodes_.at(root);
        values[node.variable] = node.low == False;
        root = node.low == False ? node.high : node.low;
    }
    return values;
}
bool Diagram::evaluate(Id root, const std::vector<bool>& values) const {
    while (root > True) {
        const auto node = nodes_.at(root);
        root = values.at(node.variable) ? node.high : node.low;
    }
    return root == True;
}
mpz_class Diagram::count(Id root, std::vector<Variable> variables) {
    std::sort(variables.begin(),variables.end());
    if(std::adjacent_find(variables.begin(),variables.end())!=variables.end())
        throw Unsupported("count projection contains duplicate Boolean variables");
    resources.tick(variables.size());
    std::map<std::pair<Id,std::size_t>,mpz_class> memo;
    std::function<mpz_class(Id,std::size_t)> visit=[&](Id id,std::size_t start)->mpz_class {
        Resources::Frame frame(resources);
        if(id==False)return 0;
        if(id==True)return mpz_class(1)<<(variables.size()-start);
        const auto key=std::pair{id,start};if(auto it=memo.find(key);it!=memo.end())return it->second;
        const auto node=nodes_.at(id);
        auto pos=std::lower_bound(variables.begin()+start,variables.end(),node.variable);
        if(pos==variables.end() || *pos!=node.variable)throw Unsupported("count formula contains an unprojected variable");
        const auto rank=std::size_t(pos-variables.begin());
        mpz_class count=visit(node.low,rank+1)+visit(node.high,rank+1);
        count<<=rank-start;memo[key]=count;return count;
    };
    return visit(root,0);
}
}
