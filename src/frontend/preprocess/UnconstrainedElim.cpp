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

bool UnconstrainedElim::run() {
    didRun_ = true;
    eliminated_ = 0;
    dropped_.clear();
    prepare();

    for (size_t idx = 0; idx < conjuncts_.size(); ++idx) {
        const auto& node = ir_.get(conjuncts_[idx].second);
        bool isRel = true;
        bool isEq = false;
        switch (node.kind) {
            case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
            case Kind::Distinct: break;
            case Kind::Eq: isEq = true; break;  // NEW: handled with elim semantics
            default: isRel = false; break;
        }
        if (!isRel || node.children.size() != 2) continue;

        ExprId lhs = node.children[0], rhs = node.children[1];
        std::string varName;
        ExprId bound = NullExpr;
        bool xIsLeft = false;
        if (auto n = asNumericVar(lhs)) { varName = *n; bound = rhs; xIsLeft = true; }
        else if (auto n2 = asNumericVar(rhs)) { varName = *n2; bound = lhs; xIsLeft = false; }
        else continue;

        // x must occur exactly once (only here) and not be a shared UF/array term.
        if (occ_[varName] != 1) continue;
        if (unsafe_.count(varName)) continue;

        SortId sort = ir_.get(xIsLeft ? lhs : rhs).sort;

        if (isEq) {
            // (= x t) where x's only global occurrence is here. Soundness:
            // x is otherwise free, so dropping the equality is equisat (extend
            // any model of the rest by setting x := eval(t, model)). No need
            // for isLinearReconstructable since the witness IS t directly
            // — ModelConverter::registerElimination tells the converter to
            // evaluate `bound` under the final model and assign that value
            // to x in the displayed model.
            mc_.registerElimination(varName, sort, bound);
            dropped_.push_back(idx);
            ++eliminated_;
            continue;
        }

        // Relational case (existing): need isLinearReconstructable so the
        // witness (b, b, b+1, b-1, b+1) can be computed exactly under model.
        if (!isLinearReconstructable(bound)) continue;

        ModelConverter::Rel relForX;
        switch (node.kind) {
            case Kind::Lt:  relForX = xIsLeft ? ModelConverter::Rel::Lt : ModelConverter::Rel::Gt; break;
            case Kind::Leq: relForX = xIsLeft ? ModelConverter::Rel::Le : ModelConverter::Rel::Ge; break;
            case Kind::Gt:  relForX = xIsLeft ? ModelConverter::Rel::Gt : ModelConverter::Rel::Lt; break;
            case Kind::Geq: relForX = xIsLeft ? ModelConverter::Rel::Ge : ModelConverter::Rel::Le; break;
            case Kind::Distinct: relForX = ModelConverter::Rel::Ne; break;
            default: continue;
        }

        mc_.registerWitness(varName, sort, relForX, bound);
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
