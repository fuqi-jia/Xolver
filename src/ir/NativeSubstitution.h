#pragma once
#include "ir/NativeBuilder.h"
#include <map>

namespace xolver::native {
// Simultaneous, identity-based substitution. The caller owns binder freshness;
// a bound node and a same-named free node are different substitution keys.
inline Node substitute(Node n, const std::map<Node, Node> &replacements, std::map<Node, Node> &memo,
                       Nodes &builder) {
    Nodes::Frame frame(builder);
    if (auto it = replacements.find(n); it != replacements.end())
        return it->second;
    if (auto it = memo.find(n); it != memo.end())
        return it->second;
    if (!n || !n->getSort())
        throw std::invalid_argument("null substitution expression");
    if (!n->getChildrenSize())
        return n;
    std::vector<Node> children;
    bool changed = false;
    for (auto c : SOMTParser::children(n)) {
        auto replaced = substitute(c, replacements, memo, builder);
        changed |= replaced != c;
        children.push_back(std::move(replaced));
    }
    auto result = changed ? builder.make(n->getSort(), n->getKind(), children, n->getName()) : n;
    memo[n] = result;
    return result;
}
} // namespace xolver::native
