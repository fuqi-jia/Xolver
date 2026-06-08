#pragma once

#include "expr/types.h"
#include "util/SmallVector.h"
#include <cstdint>
#include <functional>
#include <vector>

namespace xolver {

// ---------------------------------------------------------------------------
// RelevancyEngine — z3-style boolean relevancy over the Tseitin skeleton.
//
// PURPOSE (see docs/L7-relevancy-engine.md). On UltimateAutomizer BMC traces
// (cs_*) the SAT core decides ~27k boolean-structure variables that z3 never
// touches because it tracks *relevancy*: an atom is "relevant" only when it is
// needed to justify the truth of the asserted goal under the current partial
// assignment. Un-taken `ite` branches / un-witnessed `or` disjuncts stay
// irrelevant, so z3 closes the same instance in ~5 decisions.
//
// SOUNDNESS. This engine is a PURE DECISION HEURISTIC. CaDiCaL keeps every CNF
// clause (and every theory lemma); relevancy only changes WHICH unassigned
// variable cb_decide hands back. To declare SAT the core must still satisfy all
// clauses; to declare UNSAT it must still derive the empty clause. A buggy or
// incomplete relevancy set can therefore only make search faster or slower —
// never wrong. (Invariant 1 / the soundness boundary is untouched.)
//
// MODEL. The boolean skeleton is a DAG of RelNodes. Each node carries the SAT
// var whose assignment fixes its truth (`var`) and a `sign` (node is TRUE iff
// assignment(var) == sign — this makes `Not`, which shares its operand's var
// with a flipped sign, transparent). Relevancy is seeded at the asserted roots
// and propagated downward by the current assignment, mirroring z3's
// smt_relevancy: for a relevant node with a known value, mark the children that
// justify that value. Marks live on a backtrackable trail.
// ---------------------------------------------------------------------------

enum class RelKind : uint8_t {
    Leaf,     // theory atom / boolean variable / constant — no boolean children
    Not,      // transparent: relevant ⇒ operand (children[0]) relevant
    And,      // TRUE ⇒ all children; FALSE ⇒ the false children (witnesses)
    Or,       // FALSE ⇒ all children; TRUE ⇒ the true children (witnesses)
    Implies,  // children[0]=antecedent, [1]=consequent  (== Or(¬ant, cons))
    Ite,      // children[0]=cond, [1]=then, [2]=else (boolean ITE); cond always relevant
    Iff,      // boolean Eq / Xor / 2-ary Distinct: both children relevant
};

struct RelNode {
    RelKind kind = RelKind::Leaf;
    SatVar  var  = 0;     // SAT var whose assignment fixes this node's truth
    bool    sign = true;  // node is TRUE iff assignment(var) == sign
    SmallVector<uint32_t, 4> children;  // child node ids
};

class RelevancyEngine {
public:
    static constexpr uint32_t kNoNode = 0xFFFFFFFFu;

    // ---- construction (before finalize) ----
    // Returns the new node id. `children` are node ids returned by prior addNode.
    uint32_t addNode(RelKind kind, SatVar var, bool sign,
                     const std::vector<uint32_t>& children = {});
    void addRoot(uint32_t nodeId);

    // Value oracle: +1 if `var` is currently assigned TRUE, -1 if FALSE, 0 if
    // unassigned. Supplied by the propagator (reads its assignment map).
    void setValueOracle(std::function<int(SatVar)> oracle) { valueOf_ = std::move(oracle); }

    // Build var→node / parent indices, seed roots relevant. Call once after all
    // addNode/addRoot. Safe to call before solving (values still unknown).
    void finalize();
    bool finalized() const { return finalized_; }

    // ---- search hooks (during solve) ----
    void onAssign(SatVar var, bool value);  // an observed var just became assigned
    void pushLevel();                       // notify_new_decision_level
    void popToLevel(int level);             // notify_backtrack(level)

    // L13 integrated engine: force a DYNAMIC atom (created after finalize, e.g. a
    // Row2 case-split's i=j / readEq literal) to be relevant, so cb_decide steers
    // CaDiCaL to DECIDE it. Resizes the var-indexed maps for vars beyond the static
    // graph. Permanently relevant (not trail-managed) — a split we introduced is
    // always worth deciding. Pure decision heuristic — soundness-neutral.
    void forceRelevantVar(SatVar var);

    // ---- queries ----
    bool isRelevantVar(SatVar var) const {
        return var < varRelevantCount_.size() && varRelevantCount_[var] > 0;
    }
    // A relevant + currently-unassigned var, or 0 if none found within maxProbe
    // steps of the round-robin cursor over ever-relevant vars.
    SatVar pickRelevantUnassigned(size_t maxProbe = 256);

    // ---- diagnostics ----
    size_t totalNodes()       const { return nodes_.size(); }
    size_t relevantNodes()    const { return relevantCount_; }
    size_t relevantVarsSeen() const { return relevantVarList_.size(); }

private:
    int  nodeValue(uint32_t id) const;  // +1/-1/0 with sign applied
    void markRelevant(uint32_t id);
    void propagateNode(uint32_t id);    // apply value→relevancy rule for one node
    void drain();

    std::vector<RelNode>  nodes_;
    std::vector<uint32_t> roots_;
    std::function<int(SatVar)> valueOf_;
    bool finalized_ = false;
    SatVar maxVar_ = 0;

    std::vector<char>   relevant_;       // by node id
    size_t              relevantCount_ = 0;

    std::vector<std::vector<uint32_t>> varToNodes_;  // SatVar -> node ids
    std::vector<std::vector<uint32_t>> parents_;     // node id -> parent node ids
    std::vector<uint32_t> varRelevantCount_;         // SatVar -> #relevant nodes
    std::vector<char>     varListed_;                // SatVar -> in relevantVarList_
    std::vector<SatVar>   relevantVarList_;          // ever-relevant vars (decide ring)
    size_t                decideCursor_ = 0;

    std::vector<uint32_t> trail_;        // marked node ids, in mark order
    std::vector<size_t>   levelStart_;   // levelStart_[k] = trail size at start of level k+1

    std::vector<uint32_t> work_;         // propagation worklist (reused)
};

} // namespace xolver
