#include "frontend/preprocess/SolveEqs.h"

namespace zolver {

SolveEqs::SolveEqs(CoreIr& ir, ModelConverter& mc)
    : ir_(ir), mc_(mc),
      boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()), realSortId_(ir.realSortId()) {}

std::optional<std::string> SolveEqs::asNumericVar(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind != Kind::Variable) return std::nullopt;
    if (node.sort != intSortId_ && node.sort != realSortId_) return std::nullopt;
    if (auto* nm = std::get_if<std::string>(&node.payload.value)) return *nm;
    return std::nullopt;
}

bool SolveEqs::occurs(const std::string& name, ExprId root) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        const auto& node = ir_.get(stack.back());
        stack.pop_back();
        if (node.kind == Kind::Variable) {
            if (auto* nm = std::get_if<std::string>(&node.payload.value)) {
                if (*nm == name) return true;
            }
        }
        for (ExprId c : node.children) stack.push_back(c);
    }
    return false;
}

bool SolveEqs::isLinearReconstructable(ExprId root) const {
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
                // Linear: at most one non-constant operand.
                int nonConst = 0;
                for (ExprId c : node.children) {
                    Kind ck = ir_.get(c).kind;
                    if (ck != Kind::ConstInt && ck != Kind::ConstReal) ++nonConst;
                }
                if (nonConst > 1) return false;  // var*var etc.
                for (ExprId c : node.children) stack.push_back(c);
                break;
            }
            default:
                return false;  // div/mod/pow/to_int/uf/ite/array/... not reconstructable here
        }
    }
    return true;
}

ExprId SolveEqs::substitute(ExprId root, const std::string& name, ExprId replacement) {
    if (auto it = substMemo_.find(root); it != substMemo_.end()) return it->second;

    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (substMemo_.find(e) != substMemo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: ir_.add() may relocate exprs_

        if (node.kind == Kind::Variable) {
            bool match = false;
            if (auto* nm = std::get_if<std::string>(&node.payload.value)) match = (*nm == name);
            substMemo_[e] = match ? replacement : e;
            stack.pop_back();
            continue;
        }

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { substMemo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (substMemo_.find(c) == substMemo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        SmallVector<ExprId, 4> newChildren;
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = substMemo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        if (!changed) {
            substMemo_[e] = e;
        } else {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            fresh.children = std::move(newChildren);
            fresh.payload = node.payload;
            substMemo_[e] = ir_.add(std::move(fresh));
        }
    }
    return substMemo_.at(root);
}

void SolveEqs::computeUnsafeVars() {
    unsafeVars_.clear();
    struct F { ExprId e; bool underUF; };
    for (const auto& [level, root] : conjuncts_) {
        (void)level;
        std::vector<F> stack{{root, false}};
        while (!stack.empty()) {
            F f = stack.back();
            stack.pop_back();
            const auto& node = ir_.get(f.e);
            if (f.underUF && node.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&node.payload.value)) unsafeVars_.insert(*nm);
            }
            const bool childUnderUF = f.underUF ||
                node.kind == Kind::UFApply || node.kind == Kind::Select || node.kind == Kind::Store;
            for (ExprId c : node.children) stack.push_back({c, childUnderUF});
        }
    }
}

bool SolveEqs::run() {
    didRun_ = true;
    eliminated_ = 0;
    conjuncts_.clear();

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

    // Variables feeding an uninterpreted-function/array argument are shared
    // terms in Nelson-Oppen combination; eliminating them is unsound. Pin them.
    computeUnsafeVars();

    bool progress = true;
    while (progress) {
        progress = false;
        for (size_t idx = 0; idx < conjuncts_.size(); ++idx) {
            ExprId c = conjuncts_[idx].second;
            const auto& node = ir_.get(c);
            if (node.kind != Kind::Eq || node.children.size() != 2) continue;
            ExprId lhs = node.children[0], rhs = node.children[1];

            std::string varName;
            ExprId defExpr = NullExpr;
            SortId varSort = NullSort;
            if (auto n = asNumericVar(lhs); n && !occurs(*n, rhs) && isLinearReconstructable(rhs)) {
                varName = *n; defExpr = rhs; varSort = ir_.get(lhs).sort;
            } else if (auto n2 = asNumericVar(rhs); n2 && !occurs(*n2, lhs) && isLinearReconstructable(lhs)) {
                varName = *n2; defExpr = lhs; varSort = ir_.get(rhs).sort;
            } else {
                continue;
            }

            // Never eliminate a variable shared into a UF/array argument: doing
            // so severs a Nelson-Oppen shared term (false-SAT in combination).
            if (unsafeVars_.count(varName)) continue;

            // Eliminate: drop this equality, substitute var -> defExpr everywhere else.
            conjuncts_.erase(conjuncts_.begin() + static_cast<long>(idx));
            substMemo_.clear();
            for (auto& cj : conjuncts_) cj.second = substitute(cj.second, varName, defExpr);
            mc_.registerElimination(varName, varSort, defExpr);
            ++eliminated_;
            progress = true;
            break;  // indices shifted; restart scan
        }
    }
    return eliminated_ > 0;
}

void SolveEqs::commit() {
    if (eliminated_ == 0) return;
    ir_.clearAssertions();
    for (const auto& [level, e] : conjuncts_) ir_.addAssertion(e, level);
}

} // namespace zolver
