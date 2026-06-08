#include "sat/RelevancyEngine.h"

#include <algorithm>

namespace xolver {

uint32_t RelevancyEngine::addNode(RelKind kind, SatVar var, bool sign,
                                  const std::vector<uint32_t>& children) {
    RelNode n;
    n.kind = kind;
    n.var = var;
    n.sign = sign;
    for (uint32_t c : children) n.children.push_back(c);
    uint32_t id = static_cast<uint32_t>(nodes_.size());
    nodes_.push_back(std::move(n));
    if (var > maxVar_) maxVar_ = var;
    return id;
}

void RelevancyEngine::addRoot(uint32_t nodeId) { roots_.push_back(nodeId); }

void RelevancyEngine::finalize() {
    if (finalized_) return;
    const size_t N = nodes_.size();
    relevant_.assign(N, 0);
    parents_.assign(N, {});

    const size_t V = static_cast<size_t>(maxVar_) + 1;
    varToNodes_.assign(V, {});
    varRelevantCount_.assign(V, 0);
    varListed_.assign(V, 0);

    for (uint32_t id = 0; id < N; ++id) {
        const RelNode& n = nodes_[id];
        if (n.var < V) varToNodes_[n.var].push_back(id);
        for (uint32_t c : n.children) {
            if (c < N) parents_[c].push_back(id);
        }
    }

    finalized_ = true;

    // Seed: every asserted root is permanently relevant (marks made now live in
    // the level-0 trail segment, never undone). Propagation is a no-op until the
    // first assignments arrive (values still unknown), but Ite conditions and
    // Not operands are marked structurally here.
    for (uint32_t r : roots_) markRelevant(r);
    drain();
}

int RelevancyEngine::nodeValue(uint32_t id) const {
    const RelNode& n = nodes_[id];
    int raw = valueOf_ ? valueOf_(n.var) : 0;
    if (raw == 0) return 0;
    bool varTrue = raw > 0;
    bool nodeTrue = (varTrue == n.sign);
    return nodeTrue ? 1 : -1;
}

void RelevancyEngine::markRelevant(uint32_t id) {
    if (id >= relevant_.size() || relevant_[id]) return;
    relevant_[id] = 1;
    ++relevantCount_;
    trail_.push_back(id);

    SatVar v = nodes_[id].var;
    if (v < varRelevantCount_.size()) {
        ++varRelevantCount_[v];
        if (!varListed_[v]) {
            varListed_[v] = 1;
            relevantVarList_.push_back(v);
        }
    }
    work_.push_back(id);  // (re)propagate from this node once it has a value
}

void RelevancyEngine::propagateNode(uint32_t id) {
    const RelNode& n = nodes_[id];
    const int v = nodeValue(id);
    switch (n.kind) {
        case RelKind::Leaf:
            break;
        case RelKind::Not:
            if (!n.children.empty()) markRelevant(n.children[0]);
            break;
        case RelKind::And:
            if (v > 0) {
                for (uint32_t c : n.children) markRelevant(c);
            } else if (v < 0) {
                for (uint32_t c : n.children)
                    if (nodeValue(c) < 0) markRelevant(c);  // false witness(es)
            }
            break;
        case RelKind::Or:
            if (v < 0) {
                for (uint32_t c : n.children) markRelevant(c);
            } else if (v > 0) {
                for (uint32_t c : n.children)
                    if (nodeValue(c) > 0) markRelevant(c);   // true witness(es)
            }
            break;
        case RelKind::Implies: {
            // Implies(a,b): the GUARD `a` is always needed to know the
            // implication's truth, so it is always relevant (and thus
            // decidable). The BODY `b` is relevant only once the guard is true
            // (a true -> b forced; or the implication is false, which also
            // forces a true). When the guard is false the body is a dead branch
            // and stays pruned. This single pair of marks covers every value of
            // the implication node itself, so `v` is not consulted.
            (void)v;
            if (n.children.size() < 2) break;
            uint32_t a = n.children[0], b = n.children[1];
            markRelevant(a);
            if (nodeValue(a) > 0) markRelevant(b);
            break;
        }
        case RelKind::Ite: {
            if (n.children.size() < 3) break;
            uint32_t c = n.children[0], t = n.children[1], e = n.children[2];
            markRelevant(c);  // condition is always relevant once the Ite is
            int cv = nodeValue(c);
            if (cv > 0) markRelevant(t);
            else if (cv < 0) markRelevant(e);
            break;
        }
        case RelKind::Iff:
            for (uint32_t c : n.children) markRelevant(c);
            break;
    }
}

void RelevancyEngine::drain() {
    // work_ may grow during iteration (markRelevant pushes). Index-walk so we
    // process every scheduled node exactly in FIFO order, then clear.
    for (size_t i = 0; i < work_.size(); ++i) {
        propagateNode(work_[i]);
    }
    work_.clear();
}

void RelevancyEngine::onAssign(SatVar var, bool /*value*/) {
    if (!finalized_ || var >= varToNodes_.size()) return;
    for (uint32_t id : varToNodes_[var]) {
        // The node just got a value -> re-run its own rule (may descend now).
        if (relevant_[id]) work_.push_back(id);
        // A relevant parent may now find its witness / taken branch.
        for (uint32_t p : parents_[id])
            if (relevant_[p]) work_.push_back(p);
    }
    drain();
}

void RelevancyEngine::pushLevel() {
    levelStart_.push_back(trail_.size());
}

void RelevancyEngine::popToLevel(int level) {
    if (level < 0) level = 0;
    while (static_cast<int>(levelStart_.size()) > level) {
        size_t start = levelStart_.back();
        levelStart_.pop_back();
        while (trail_.size() > start) {
            uint32_t id = trail_.back();
            trail_.pop_back();
            if (relevant_[id]) {
                relevant_[id] = 0;
                --relevantCount_;
                SatVar v = nodes_[id].var;
                if (v < varRelevantCount_.size() && varRelevantCount_[v] > 0)
                    --varRelevantCount_[v];
            }
        }
    }
}

SatVar RelevancyEngine::pickRelevantUnassigned(size_t maxProbe) {
    const size_t n = relevantVarList_.size();
    if (n == 0 || !valueOf_) return 0;
    const size_t probes = std::min(n, maxProbe);
    for (size_t i = 0; i < probes; ++i) {
        SatVar v = relevantVarList_[decideCursor_];
        decideCursor_ = (decideCursor_ + 1) % n;
        if (v < varRelevantCount_.size() && varRelevantCount_[v] > 0 &&
            valueOf_(v) == 0) {
            return v;
        }
    }
    return 0;
}

} // namespace xolver
