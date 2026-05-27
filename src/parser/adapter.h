#pragma once

#include "expr/ir.h"
#include <somtparser/frontend/parser.h>
#include <somtparser/ir/dag.h>
#include <somtparser/ir/node.h>
#include <unordered_map>

namespace zolver {

/**
 * FrontendAdapter: converts SOMTParser AST (Node = shared_ptr<DAGNode>)
 * into Zolver internal CoreIr (ExprId-based dense array).
 *
 * Uses unordered_map<Node, ExprId, NodeHash, NodeEqual> for memoization,
 * leveraging SOMTParser's existing hash-consing.
 */
class FrontendAdapter {
public:
    explicit FrontendAdapter(SOMTParser::Parser& parser);

    // Import all assertions from parser into a fresh CoreIr.
    std::unique_ptr<CoreIr> importProblem();

    SortId getBoolSortId() const { return boolSortId_; }

private:
    ExprId importNode(SOMTParser::Node node);
    SortId mapSort(SOMTParser::Node node);
    SortId mapSort(std::shared_ptr<SOMTParser::Sort> sort);
    Kind mapKind(SOMTParser::NODE_KIND nk);
    Payload extractPayload(SOMTParser::Node node);

    // Translate SOMTParser declare-datatypes metadata for `sort` (already
    // assigned `id`) into the CoreIr DatatypeRegistry. Idempotent. Recurses
    // into selector arg sorts via mapSort; safe on recursive datatypes because
    // `id` is memoized before this is called.
    void populateDatatype(SortId id, const std::shared_ptr<SOMTParser::Sort>& sort);

    SOMTParser::Parser& parser_;
    std::unique_ptr<CoreIr> ir_;
    SortId boolSortId_ = NullSort;

    // ZOLVER_PP_LET_ELIM: eliminate residual let nodes at import time. SOMTParser
    // preserves lets and its expandLet only expands the outermost one, so a let
    // nested in a binding VALUE or an operand position survives as a let_chain
    // that mapKind cannot map (-> Unknown -> unknown verdict). When set, a
    // let_bind_var is imported as its bound value and a let/let_chain as its
    // body, which collapses arbitrary nesting via the node memo. Read once from
    // the environment in importProblem.
    bool letElim_ = false;

    // Memo: each SOMTParser Node maps to exactly one ExprId.
    std::unordered_map<
        SOMTParser::Node,
        ExprId,
        SOMTParser::NodeHash,
        SOMTParser::NodeEqual
    > memo_;

    // Sort memo: SOMTParser Sort → internal SortId.
    struct SpSortHash {
        size_t operator()(const std::shared_ptr<SOMTParser::Sort>& s) const {
            return s->hash();
        }
    };
    struct SpSortEqual {
        bool operator()(const std::shared_ptr<SOMTParser::Sort>& a,
                        const std::shared_ptr<SOMTParser::Sort>& b) const {
            return *a == *b;
        }
    };
    std::unordered_map<
        std::shared_ptr<SOMTParser::Sort>,
        SortId,
        SpSortHash,
        SpSortEqual
    > sortMemo_;
};

} // namespace zolver
