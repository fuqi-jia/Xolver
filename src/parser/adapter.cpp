#include "parser/adapter.h"
#include "expr/rewriter.h"
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>

namespace xolver {

using namespace SOMTParser;

FrontendAdapter::FrontendAdapter(Parser& parser) : parser_(parser) {}

std::unique_ptr<CoreIr> FrontendAdapter::importProblem() {
    ir_ = std::make_unique<CoreIr>();
    memo_.clear();
    sortMemo_.clear();
    // Import-time let-elimination collapses the residual nested let_chain nodes
    // that SOMTParser::expandLet leaves behind (it expands only the outermost
    // let). XOLVER_COMB_ARRAY_NIA implies it: the array+NIA benchmarks
    // (Ultimate-Automizer SV-COMP) are let-heavy, and without elimination the
    // let nodes map to Kind::Unknown and corrupt the formula. The pass is
    // capture-free and idempotent on non-let nodes (z3-validated), so coupling
    // it on is behavior-neutral for let-free input.
    letElim_ = (std::getenv("XOLVER_PP_LET_ELIM") != nullptr) ||
               (std::getenv("XOLVER_COMB_ARRAY_NIA") != nullptr);

    // Stage A: run SOMTParser rewriter before conversion.
    SOMTParser::Rewriter rewriter(parser_.getNodeManager());
    SOMTParser::installDefaultRewriteRules(rewriter);
    installXolverRewriteRules(rewriter);

    for (Node assertion : parser_.getAssertions()) {
        Node rewritten = rewriter.rewrite(assertion);
        // Expand preserving-let nodes before CoreIr import.
        // SOMTParser's expandLet is iterative and idempotent on non-let nodes.
        Node expanded = parser_.expandLet(rewritten);
        ExprId id = importNode(expanded);
        ir_->addAssertion(id);
    }
    return std::move(ir_);
}

ExprId FrontendAdapter::importNode(Node node) {
    if (!node) return NullExpr;

    auto it = memo_.find(node);
    if (it != memo_.end()) return it->second;

    // Iterative post-order traversal to avoid stack overflow on deep DAGs.
    struct Frame {
        Node node;
        size_t nextChild;
    };

    std::vector<Frame> stack;
    std::unordered_set<Node> visited;
    stack.reserve(1024);
    visited.reserve(1024);

    stack.push_back({node, 0});
    visited.insert(node);

    while (!stack.empty()) {
        Frame& frame = stack.back();

        // Push unprocessed children first
        if (frame.nextChild < numChildren(frame.node)) {
            Node c = child(frame.node, frame.nextChild);
            ++frame.nextChild;

            if (c) {
                auto memoIt = memo_.find(c);
                if (memoIt == memo_.end() && visited.find(c) == visited.end()) {
                    stack.push_back({c, 0});
                    visited.insert(c);
                }
            }
            continue;
        }

        // All children processed — create CoreExpr for this node
        Node n = frame.node;
        stack.pop_back();
        visited.erase(n);

        std::vector<ExprId> childIds;
        childIds.reserve(numChildren(n));
        for (size_t i = 0; i < numChildren(n); ++i) {
            Node c = child(n, i);
            if (!c) continue;
            auto memoIt = memo_.find(c);
            if (memoIt != memo_.end()) {
                childIds.push_back(memoIt->second);
            }
        }

        // Import-time let elimination (XOLVER_PP_LET_ELIM). Substitution by node
        // identity: a let_bind_var IS its bound value (child 0); a let/let_chain
        // IS its body (child 0 / last child). The body references each bound var
        // as the SAME shared node, so this single post-order pass collapses
        // arbitrary nesting that SOMTParser::expandLet left behind. Capture-free
        // (SOMTParser binds by node, not by name).
        if (letElim_) {
            SOMTParser::NODE_KIND lk = kind(n);
            if (lk == SOMTParser::NODE_KIND::NT_LET_BIND_VAR) {
                Node v = (numChildren(n) > 0) ? child(n, 0) : nullptr;
                ExprId vid = NullExpr;
                if (v) { auto mi = memo_.find(v); if (mi != memo_.end()) vid = mi->second; }
                memo_[n] = vid;
                continue;
            }
            if (lk == SOMTParser::NODE_KIND::NT_LET ||
                lk == SOMTParser::NODE_KIND::NT_LET_CHAIN) {
                ExprId bid = NullExpr;
                size_t nc = numChildren(n);
                if (nc > 0) {
                    size_t bi = (lk == SOMTParser::NODE_KIND::NT_LET) ? 0 : (nc - 1);
                    Node b = child(n, bi);
                    if (b) { auto mi = memo_.find(b); if (mi != memo_.end()) bid = mi->second; }
                }
                memo_[n] = bid;
                continue;
            }
            if (lk == SOMTParser::NODE_KIND::NT_LET_BIND_VAR_LIST) {
                memo_[n] = NullExpr;  // structural; never used as a value
                continue;
            }
        }

        SOMTParser::NODE_KIND nk = kind(n);
        Kind k = mapKind(nk);
        if (k == Kind::Unknown) {
            std::cerr << "[FrontendAdapter] WARNING: unmapped SOMTParser node kind="
                      << static_cast<int>(nk) << " name='" << n->getName()
                      << "' children=" << numChildren(n) << "\n";
        }
        if (k == Kind::ConstReal) {
            auto sn = sort(n);
            if (sn && sn->isInt()) k = Kind::ConstInt;
        }
        SortId s = mapSort(n);
        Payload p = extractPayload(n);

        // Infer sort for numeric constants when parser gives no explicit sort.
        if (s == NullSort && k == Kind::ConstReal) {
            if (auto* str = std::get_if<std::string>(&p.value)) {
                bool isDecimal = (str->find('.') != std::string::npos) ||
                                 (str->find('/') != std::string::npos);
                if (!isDecimal) {
                    k = Kind::ConstInt;
                    s = ir_->intSortId();
                    if (s == NullSort) {
                        s = ir_->allocateSortId();
                        ir_->setIntSortId(s);
                        ir_->registerSort(s, SortKind::Int);
                    }
                } else {
                    s = ir_->realSortId();
                    if (s == NullSort) {
                        s = ir_->allocateSortId();
                        ir_->setRealSortId(s);
                        ir_->registerSort(s, SortKind::Real);
                    }
                }
            }
        }

        // Flip > and >= to < and <= by swapping children.
        if (nk == SOMTParser::NODE_KIND::NT_GT) {
            k = Kind::Lt;
            std::swap(childIds[0], childIds[1]);
        } else if (nk == SOMTParser::NODE_KIND::NT_GE) {
            k = Kind::Leq;
            std::swap(childIds[0], childIds[1]);
        }

        CoreExpr expr;
        expr.kind = k;
        expr.sort = s;
        expr.children = SmallVector<ExprId, 4>(childIds.begin(), childIds.end());
        expr.payload = std::move(p);

        ExprId id = ir_->add(std::move(expr));
        memo_[n] = id;
    }

    return memo_[node];
}

SortId FrontendAdapter::mapSort(Node node) {
    return mapSort(sort(node));
}

SortId FrontendAdapter::mapSort(std::shared_ptr<SOMTParser::Sort> sort) {
    if (!sort) return NullSort;

    // Canonicalize basic sorts so that SK_DEC/SK_DEF forms of Int/Real/Bool
    // map to the same SortId as the canonical SK_INT/SK_REAL/SK_BOOL forms.
    if ((sort->isDec() || sort->isDef()) && sort->arity == 0) {
        if (sort->name == "Int") {
            sort = SOMTParser::SortManager::getInt();
        } else if (sort->name == "Real") {
            sort = SOMTParser::SortManager::getReal();
        } else if (sort->name == "Bool") {
            sort = SOMTParser::SortManager::getBool();
        }
    }
    // SOMTParser represents integer numerals as SK_INTOREAL.  Map them to Int.
    if (sort->isIntOrReal()) {
        sort = SOMTParser::SortManager::getInt();
    }

    auto it = sortMemo_.find(sort);
    if (it != sortMemo_.end()) return it->second;

    SortId id = static_cast<SortId>(sortMemo_.size());
    sortMemo_[sort] = id;

    if (sort->isBool() && boolSortId_ == NullSort) {
        boolSortId_ = id;
    }
    if (sort->isInt() && ir_->intSortId() == NullSort) {
        ir_->setIntSortId(id);
    }
    if (sort->isReal() && ir_->realSortId() == NullSort) {
        ir_->setRealSortId(id);
    }

    // Register sort kind in CoreIr
    SortKind kind = SortKind::Other;
    if (sort->isBool()) kind = SortKind::Bool;
    else if (sort->isInt()) kind = SortKind::Int;
    else if (sort->isReal()) kind = SortKind::Real;
    else if (sort->isBv()) kind = SortKind::BV;
    else if (sort->isFp()) kind = SortKind::FP;
    else if (sort->isArray()) kind = SortKind::Array;
    else if (sort->isDatatype()) kind = SortKind::Datatype;
    ir_->registerSort(id, kind);

    // Record (index, elem) sorts for Array sorts so the array theory and model
    // output can recover them (SortId is otherwise opaque). Safe to recurse:
    // this sort is already memoized above, so a self-referential nesting cannot
    // loop.
    if (sort->isArray()) {
        SortId idxId = mapSort(sort->getIndexSort());
        SortId elemId = mapSort(sort->getElemSort());
        ir_->registerArraySort(id, idxId, elemId);
    }

    // Translate datatype constructor/selector signatures into the registry.
    // `id` is already memoized above, so recursive datatypes (a selector whose
    // result sort is the datatype itself) resolve to this same id without loop.
    if (sort->isDatatype()) {
        populateDatatype(id, sort);
    }

    return id;
}

void FrontendAdapter::populateDatatype(SortId id,
                                       const std::shared_ptr<SOMTParser::Sort>& sort) {
    if (!sort || !sort->isDatatype()) return;
    if (ir_->datatypes().isDatatypeSort(id)) return;  // idempotent

    DatatypeInfo info;
    info.sort = id;
    info.recursive = parser_.isRecursiveDatatype(sort);

    uint32_t ctorIdx = 0;
    for (const auto& ctor : sort->getDtConstructors()) {
        DtConstructorInfo ci;
        ci.name = ctor.name;
        ci.index = ctorIdx++;
        for (const auto& sel : ctor.selectors) {
            DtSelectorInfo si;
            si.name = sel.name;
            si.resultSort = mapSort(sel.sort);  // safe: `id` already memoized
            ci.selectors.push_back(std::move(si));
        }
        info.constructors.push_back(std::move(ci));
    }
    ir_->datatypes().addDatatype(std::move(info));
}

Kind FrontendAdapter::mapKind(SOMTParser::NODE_KIND nk) {
    switch (nk) {
        case NODE_KIND::NT_CONST_TRUE:  return Kind::ConstBool;
        case NODE_KIND::NT_CONST_FALSE: return Kind::ConstBool;
        case NODE_KIND::NT_CONST:       return Kind::ConstReal; // refined by payload later
        case NODE_KIND::NT_VAR:         return Kind::Variable;
        case NODE_KIND::NT_UF_APPLY:    return Kind::UFApply;
        case NODE_KIND::NT_FUNC_APPLY:  return Kind::UFApply;
        case NODE_KIND::NT_AND:         return Kind::And;
        case NODE_KIND::NT_OR:          return Kind::Or;
        case NODE_KIND::NT_NOT:         return Kind::Not;
        case NODE_KIND::NT_IMPLIES:     return Kind::Implies;
        case NODE_KIND::NT_XOR:         return Kind::Xor;
        case NODE_KIND::NT_ITE:         return Kind::Ite;
        case NODE_KIND::NT_EQ:          return Kind::Eq;
        case NODE_KIND::NT_DISTINCT:    return Kind::Distinct;
        case NODE_KIND::NT_ADD:         return Kind::Add;
        case NODE_KIND::NT_SUB:         return Kind::Sub;
        case NODE_KIND::NT_NEG:         return Kind::Neg;
        case NODE_KIND::NT_MUL:         return Kind::Mul;
        case NODE_KIND::NT_DIV_REAL:
        case NODE_KIND::NT_DIV_INT:     return Kind::Div;
        case NODE_KIND::NT_MOD:         return Kind::Mod;
        case NODE_KIND::NT_ABS:         return Kind::Abs;
        case NODE_KIND::NT_POW:         return Kind::Pow;
        case NODE_KIND::NT_LE:          return Kind::Leq;
        case NODE_KIND::NT_LT:          return Kind::Lt;
        case NODE_KIND::NT_GE:          return Kind::Geq;
        case NODE_KIND::NT_GT:          return Kind::Gt;
        case NODE_KIND::NT_BV_NOT:      return Kind::BvNot;
        case NODE_KIND::NT_BV_AND:      return Kind::BvAnd;
        case NODE_KIND::NT_BV_OR:       return Kind::BvOr;
        case NODE_KIND::NT_BV_ADD:      return Kind::BvAdd;
        case NODE_KIND::NT_BV_MUL:      return Kind::BvMul;
        case NODE_KIND::NT_FORALL:      return Kind::Forall;
        case NODE_KIND::NT_EXISTS:      return Kind::Exists;
        case NODE_KIND::NT_TO_INT:      return Kind::ToInt;
        case NODE_KIND::NT_TO_REAL:     return Kind::ToReal;
        case NODE_KIND::NT_IS_INT:      return Kind::IsInt;
        case NODE_KIND::NT_SELECT:      return Kind::Select;
        case NODE_KIND::NT_STORE:       return Kind::Store;
        case NODE_KIND::NT_CONST_ARRAY: return Kind::ConstArray;
        case NODE_KIND::NT_DT_CONSTRUCTOR: return Kind::Constructor;
        case NODE_KIND::NT_DT_SELECTOR:    return Kind::Selector;
        case NODE_KIND::NT_DT_TESTER:      return Kind::Tester;
        default:                        return Kind::Unknown;
    }
}

Payload FrontendAdapter::extractPayload(SOMTParser::Node node) {
    if (!node) return {};

    NODE_KIND nk = kind(node);
    if (nk == NODE_KIND::NT_CONST_TRUE)  return Payload(true);
    if (nk == NODE_KIND::NT_CONST_FALSE) return Payload(false);

    if (nk == NODE_KIND::NT_CONST || nk == NODE_KIND::NT_VAR) {
        auto val = node->getValue();
        if (val) {
            switch (val->getType()) {
                case BOOLEAN:
                    return Payload(val->getBooleanValue());
                case NUMBER: {
                    auto num = val->getNumberValue();
                    // For Stage A, store all numeric constants as strings.
                    // A future refinement can distinguish int vs rational.
                    return Payload(num.toString());
                }
                case BV: {
                    // Try to parse small BV constants; fall back to string.
                    std::string name = node->getName();
                    if (name.size() > 2 && name[0] == '#') {
                        if (name[1] == 'b') {
                            uint64_t v = 0;
                            for (size_t i = 2; i < name.size() && i < 66; ++i) {
                                v = (v << 1) | (name[i] == '1');
                            }
                            return Payload(v);
                        } else if (name[1] == 'x') {
                            uint64_t v = 0;
                            for (size_t i = 2; i < name.size() && i < 18; ++i) {
                                char c = name[i];
                                v = (v << 4) | ((c >= '0' && c <= '9') ? (c - '0') :
                                                (c >= 'a' && c <= 'f') ? (c - 'a' + 10) :
                                                (c >= 'A' && c <= 'F') ? (c - 'A' + 10) : 0);
                            }
                            return Payload(v);
                        }
                    }
                    return Payload(name);
                }
                default:
                    return Payload(node->getName());
            }
        }
        // Fallback: use node name (symbol name or literal string).
        return Payload(node->getName());
    }

    if (nk == NODE_KIND::NT_UF_APPLY) {
        return Payload(node->getName());
    }

    // Datatype operators carry their operator name (constructor / selector /
    // tester symbol) so the DatatypeRegistry can resolve it later.
    if (nk == NODE_KIND::NT_DT_CONSTRUCTOR ||
        nk == NODE_KIND::NT_DT_SELECTOR ||
        nk == NODE_KIND::NT_DT_TESTER) {
        return Payload(node->getName());
    }

    return {};
}

} // namespace xolver
