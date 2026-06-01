#pragma once

#include "expr/ir.h"
#include "expr/Datatype.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <memory>
#include <unordered_map>
#include <unordered_set>

namespace xolver {

/**
 * DtModelValidator — independent end-to-end DT model check (#20/#21).
 *
 * Re-evaluates original assertions (pre-lowering ExprIds) at sat time. Datatype
 * values are extracted STRUCTURALLY from the e-graph: for each DT e-class that
 * holds a constructor term, the value is a tree (ctorName + child trees built
 * recursively from each constructor argument's e-class). Classes without a
 * constructor witness are opaque leaves identified by class id.
 *
 * Why structural rather than e-class identity? An over-merging bug in the
 * e-graph can put `(left s)` in the same class as `(stack A empty)`, but s's
 * actual constructor tree might be `Record(left=stack(B,empty), ...)`. Tree
 * extraction goes through the OPERAND's structural value, so we re-derive
 * `(left s)` = `stack(B,empty)` and Eq with `(stack A empty)` correctly
 * resolves to False — the over-merge becomes visible.
 *
 * Semantics (SMT-LIB strict):
 *   - Selector on wrong-ctor → Indeterminate (NOT a conflict). z3 confirms
 *     `(head nil) = red` is sat — selector on the wrong ctor is underspecified.
 *   - Selector on right-ctor → recursive value of that arg.
 *   - Selector on opaque (no ctor witness) → fall back to e-class identity.
 *   - Eq over DT trees: structural (ctor + children match → True; distinct
 *     ctors → False; one opaque one ctor → Indeterminate; both opaque → True
 *     iff same e-class else Indeterminate).
 *   - Tester (is-C x): True iff x's tree has ctor C; False iff has other ctor;
 *     Indeterminate iff opaque.
 *
 * Verdict (conservative):
 *   - Satisfied      : every assertion definitely true.
 *   - Violated       : some assertion definitely false (sound floor → Unknown).
 *   - Indeterminate  : can't fully evaluate, none definitely false (no floor).
 *
 * Cycle protection: tree extraction tracks in-progress classes — if a cycle is
 * encountered (which should never happen post-acyclicity DFS, but is here as a
 * defense), the class is returned as opaque.
 */
class DtModelValidator {
public:
    enum class Verdict { Satisfied, Violated, Indeterminate };

    DtModelValidator(const CoreIr& ir,
                     const EufTermManager& tm,
                     const IncrementalEGraph& egraph,
                     const DatatypeRegistry& dts)
        : ir_(ir), tm_(tm), egraph_(egraph), dts_(dts) {}

    // XOLVER_DT_VALIDATOR_STRICT (default-OFF): when set, validate() promotes
    // Indeterminate → Violated. Use when the candidate sat verdict reaches the
    // top-level under conditions where eval can't fully ground out (e.g. the
    // 5min batch surfaced 43 false-SATs the lenient mode missed). Sound but
    // over-floors true-sat cases whose model uses opaque (non-constructor) DT
    // classes — only enable when the false-SAT cost dominates lost recovery.
    void setStrictMode(bool s) { strict_ = s; }

    /** Validate the given assertion roots (original-formula ExprIds). */
    Verdict validate(const std::vector<ExprId>& assertions);

private:
    enum class Kind3 {
        Bool,            // boolean value
        DtTree,          // structural datatype value (tree)
        Number,          // numeric value
        Opaque,          // non-DT non-numeric class (e.g. uninterp scalar)
        Indeterminate    // cannot evaluate
    };

    struct Tree;
    using TreePtr = std::shared_ptr<Tree>;
    struct Tree {
        bool hasCtor = false;
        std::string ctorName;          // when hasCtor
        std::vector<TreePtr> children; // when hasCtor (one per ctor arg)
        EClassId opaqueCls = static_cast<EClassId>(-1); // when !hasCtor
    };

    struct R {
        Kind3 kind = Kind3::Indeterminate;
        bool b = false;
        EClassId cls = static_cast<EClassId>(-1);
        std::string numStr;
        TreePtr tree;
    };

    R eval(ExprId e);

    // Build the structural tree for a datatype-sorted ExprId. The tree is
    // derived from the OPERAND'S e-class (via findTerm), then by picking any
    // constructor term in the class and recursively extracting each arg.
    TreePtr extractTree(EClassId c);

    // Resolve the constructor name of an e-class, if determined. Empty if not.
    // Returns the FIRST constructor term found in classMembers (post acyclicity
    // / clash detection, all constructor terms in one class agree on name).
    std::string constructorOfClass(EClassId c) const;
    // Find the constructor term in a class whose ctor name is C, if any. Used
    // to grab the EUF args for subtree extraction.
    EufTermId constructorTermInClass(EClassId c, const std::string& ctorName) const;
    // Datatype sort of an e-class (any member's origin sort), NullSort if none.
    SortId classDatatypeSort(EClassId c) const;

    // Structural equality of two extracted trees. Returns Kind3::Bool with the
    // verdict, or Kind3::Indeterminate.
    R compareTrees(const TreePtr& a, const TreePtr& b);

    const CoreIr& ir_;
    const EufTermManager& tm_;
    const IncrementalEGraph& egraph_;
    const DatatypeRegistry& dts_;

    std::unordered_map<ExprId, R> memo_;
    std::unordered_map<EClassId, TreePtr> treeMemo_;
    std::unordered_set<EClassId> inProgress_;  // cycle guard
    bool strict_ = false;
    // Set when an SMT-LIB-underspecified situation is encountered: extracting
    // an opaque DT class (no ctor witness) OR a selector applied to a
    // sibling ctor (e.g. (head nil) when nil≠cons). Strict promotion
    // (Indet -> Violated) is GATED off when set — these cases are NOT
    // structural conflicts, so flooring them over-floors true-sats.
    // 2026-06-01 emergency fix: original strict (unconditional promote)
    // showed adverse scaling at 5min wall (2693 over-floor vs 55 at 20s).
    mutable bool sawUnderspecified_ = false;
};

} // namespace xolver
