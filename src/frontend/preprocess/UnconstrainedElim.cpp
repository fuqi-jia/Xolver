#include "frontend/preprocess/UnconstrainedElim.h"

namespace xolver {

UnconstrainedElim::UnconstrainedElim(CoreIr& ir, ModelConverter& mc)
    : ir_(ir), mc_(mc),
      boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()), realSortId_(ir.realSortId()) {}

std::optional<std::string> UnconstrainedElim::asNumericVar(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind != Kind::Variable) return std::nullopt;
    if (node.sort != intSortId_ && node.sort != realSortId_) return std::nullopt;
    if (auto* nm = std::get_if<std::string>(&node.payload.value)) return *nm;
    return std::nullopt;
}

bool UnconstrainedElim::isLinearReconstructable(ExprId root) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        const auto& node = ir_.get(stack.back());
        stack.pop_back();
        switch (node.kind) {
            case Kind::ConstInt: case Kind::ConstReal: case Kind::Variable:
                break;
            case Kind::Add: case Kind::Sub: case Kind::Neg: case Kind::ToReal:
                for (ExprId c : node.children) stack.push_back(c);
                break;
            case Kind::Mul: {
                int nonConst = 0;
                for (ExprId c : node.children) {
                    Kind ck = ir_.get(c).kind;
                    if (ck != Kind::ConstInt && ck != Kind::ConstReal) ++nonConst;
                }
                if (nonConst > 1) return false;
                for (ExprId c : node.children) stack.push_back(c);
                break;
            }
            default:
                return false;
        }
    }
    return true;
}

void UnconstrainedElim::prepare() {
    conjuncts_.clear();
    occ_.clear();
    unsafe_.clear();

    // Flatten top-level conjunctions into atomic conjuncts (keeping levels).
    for (const auto& [level, a] : ir_.getScopedAssertions()) {
        std::vector<ExprId> flat{a};
        while (!flat.empty()) {
            ExprId e = flat.back();
            flat.pop_back();
            const auto& node = ir_.get(e);
            if (node.kind == Kind::And) {
                for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i)
                    flat.push_back(node.children[i]);
            } else {
                conjuncts_.push_back({level, e});
            }
        }
    }

    // Global occurrence count + under-UF set, over every conjunct's full tree.
    struct F { ExprId e; bool underUF; };
    for (const auto& [level, root] : conjuncts_) {
        (void)level;
        std::vector<F> stack{{root, false}};
        while (!stack.empty()) {
            F f = stack.back();
            stack.pop_back();
            const auto& node = ir_.get(f.e);
            if (node.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&node.payload.value)) {
                    ++occ_[*nm];
                    if (f.underUF) unsafe_.insert(*nm);
                }
            }
            const bool childUnderUF = f.underUF ||
                node.kind == Kind::UFApply || node.kind == Kind::Select || node.kind == Kind::Store;
            for (ExprId c : node.children) stack.push_back({c, childUnderUF});
        }
    }
}

bool UnconstrainedElim::varOccursIn(const std::string& name, ExprId root) const {
    std::vector<ExprId> stack{root};
    std::unordered_set<ExprId> seen;
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        if (!seen.insert(e).second) continue;
        const auto& node = ir_.get(e);
        if (node.kind == Kind::Variable) {
            if (auto* nm = std::get_if<std::string>(&node.payload.value)) {
                if (*nm == name) return true;
            }
        }
        for (ExprId c : node.children) stack.push_back(c);
    }
    return false;
}

bool UnconstrainedElim::findDropAction(ExprId e, bool target, DropAction& out) const {
    const auto& node = ir_.get(e);

    // Not: invert target and recurse.
    if (node.kind == Kind::Not) {
        if (node.children.size() != 1) return false;
        return findDropAction(node.children[0], !target, out);
    }

    // Or: target=true is monotone (any disjunct can be the witness).
    // target=false would require ALL disjuncts to be falsifiable with
    // non-overlapping witnesses — skip (conservative).
    if (node.kind == Kind::Or) {
        if (!target) return false;
        for (ExprId c : node.children) {
            if (findDropAction(c, true, out)) return true;
        }
        return false;
    }

    // And: target=false is monotone (any conjunct false ⇒ and false).
    // target=true requires all conjuncts true — skip.
    if (node.kind == Kind::And) {
        if (target) return false;
        for (ExprId c : node.children) {
            if (findDropAction(c, false, out)) return true;
        }
        return false;
    }

    // Atom-level: Eq, Distinct, Lt, Leq, Gt, Geq.
    bool isEq = (node.kind == Kind::Eq);
    bool isDistinct = (node.kind == Kind::Distinct);
    bool isRel = (node.kind == Kind::Lt || node.kind == Kind::Leq ||
                  node.kind == Kind::Gt || node.kind == Kind::Geq);
    if (!isEq && !isDistinct && !isRel) return false;
    if (node.children.size() != 2) return false;

    ExprId lhs = node.children[0], rhs = node.children[1];
    std::string varName;
    ExprId bound = NullExpr;
    bool xIsLeft = false;
    if (auto n = asNumericVar(lhs)) { varName = *n; bound = rhs; xIsLeft = true; }
    else if (auto n2 = asNumericVar(rhs)) { varName = *n2; bound = lhs; xIsLeft = false; }
    else return false;

    if (occ_.count(varName) == 0 || occ_.at(varName) != 1) return false;
    if (unsafe_.count(varName)) return false;
    // Defensive: ensure the var truly does not appear in `bound`. (Should be
    // implied by occ==1 since the only occurrence is the var-side, but the
    // count is structural — a shared DAG node could double-count us.)
    if (varOccursIn(varName, bound)) return false;

    SortId sort = ir_.get(xIsLeft ? lhs : rhs).sort;
    out.varName = varName;
    out.sort = sort;
    out.bound = bound;

    if (isEq) {
        if (target) {
            // (= v t) → set v := t
            out.useElim = true;
        } else {
            // ¬(= v t) → set v ≠ t
            out.useElim = false;
            out.rel = ModelConverter::Rel::Ne;
        }
        return true;
    }

    if (isDistinct) {
        if (target) {
            // (distinct v t) → set v ≠ t
            out.useElim = false;
            out.rel = ModelConverter::Rel::Ne;
        } else {
            // ¬(distinct v t) → set v = t
            out.useElim = true;
        }
        return true;
    }

    // Relational: require isLinearReconstructable so the witness math is exact.
    if (!isLinearReconstructable(bound)) return false;
    ModelConverter::Rel relPos;
    switch (node.kind) {
        case Kind::Lt:  relPos = xIsLeft ? ModelConverter::Rel::Lt : ModelConverter::Rel::Gt; break;
        case Kind::Leq: relPos = xIsLeft ? ModelConverter::Rel::Le : ModelConverter::Rel::Ge; break;
        case Kind::Gt:  relPos = xIsLeft ? ModelConverter::Rel::Gt : ModelConverter::Rel::Lt; break;
        case Kind::Geq: relPos = xIsLeft ? ModelConverter::Rel::Ge : ModelConverter::Rel::Le; break;
        default: return false;
    }
    ModelConverter::Rel relNeg;
    switch (relPos) {
        case ModelConverter::Rel::Lt: relNeg = ModelConverter::Rel::Ge; break;
        case ModelConverter::Rel::Le: relNeg = ModelConverter::Rel::Gt; break;
        case ModelConverter::Rel::Gt: relNeg = ModelConverter::Rel::Le; break;
        case ModelConverter::Rel::Ge: relNeg = ModelConverter::Rel::Lt; break;
        default: relNeg = ModelConverter::Rel::Ne; break;
    }
    out.useElim = false;
    out.rel = target ? relPos : relNeg;
    return true;
}

void UnconstrainedElim::applyAction(const DropAction& a) {
    if (a.useElim) {
        mc_.registerElimination(a.varName, a.sort, a.bound);
    } else {
        mc_.registerWitness(a.varName, a.sort, a.rel, a.bound);
    }
}

bool UnconstrainedElim::run() {
    didRun_ = true;
    eliminated_ = 0;
    dropped_.clear();
    prepare();

    // Within a single run(), once we use a var as a witness in one conjunct
    // it cannot be re-used elsewhere — but the global occ_ map already
    // ensures occ==1 so reuse is impossible by construction.
    for (size_t idx = 0; idx < conjuncts_.size(); ++idx) {
        DropAction a;
        if (!findDropAction(conjuncts_[idx].second, /*target=*/true, a)) continue;
        applyAction(a);
        dropped_.push_back(idx);
        ++eliminated_;
    }

    return eliminated_ > 0;
}

void UnconstrainedElim::commit() {
    if (eliminated_ == 0) return;
    std::unordered_set<size_t> drop(dropped_.begin(), dropped_.end());
    ir_.clearAssertions();
    for (size_t idx = 0; idx < conjuncts_.size(); ++idx) {
        if (drop.count(idx)) continue;
        ir_.addAssertion(conjuncts_[idx].second, conjuncts_[idx].first);
    }
}

} // namespace xolver
