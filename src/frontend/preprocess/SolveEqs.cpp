#include "base/RuntimeConfig.h"
#include "frontend/preprocess/SolveEqs.h"
#include "algebra/linear/LinearExpr.h"
#include "base/EnvParam.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <gmpxx.h>

namespace xolver {

SolveEqs::SolveEqs(NativeTerms& ir, ModelConverter& mc, DefinitionPolicy policy)
    : ir_(ir), mc_(mc), policy_(policy),
      boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()), realSortId_(ir.realSortId()) {
    {
        long long v = config::read<config::ReadKind::Long>("XOLVER_PP_SOLVE_EQS_BUDGET",
                                     static_cast<long>(workBudget_));
        if (v > 0) workBudget_ = static_cast<uint64_t>(v);
    }
}

std::optional<std::string> SolveEqs::asNumericVar(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind != Kind::Variable) return std::nullopt;
    if (node.sort != intSortId_ && node.sort != realSortId_) return std::nullopt;
    if (auto* nm = std::get_if<std::string>(&node.payload.value)) return *nm;
    return std::nullopt;
}

bool SolveEqs::occurs(const std::string& name, ExprId root) const {
    std::vector<ExprId> stack{root};
    std::unordered_set<ExprId> seen;
    while (!stack.empty()) {
        const auto id = stack.back();
        stack.pop_back();
        if (!seen.insert(id).second) continue;
        const auto& node = ir_.get(id);
        if (node.kind == Kind::Variable) {
            if (auto* nm = std::get_if<std::string>(&node.payload.value)) {
                if (*nm == name) return true;
            }
        }
        for (ExprId c : node.children) stack.push_back(c);
    }
    return false;
}

bool SolveEqs::isReconstructable(ExprId root, bool polynomial) const {
    std::vector<ExprId> stack{root};
    std::unordered_set<ExprId> seen;
    while (!stack.empty()) {
        const auto id = stack.back();
        stack.pop_back();
        if (!seen.insert(id).second) continue;
        const auto& node = ir_.get(id);
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
                if (!polynomial && nonConst > 1) return false;
                for (ExprId c : node.children) stack.push_back(c);
                break;
            }
            default:
                return false;  // div/mod/pow/to_int/uf/ite/array/... not reconstructable here
        }
    }
    return true;
}

bool SolveEqs::admissibleDefinition(const std::string& name, ExprId e) {
    if (isReconstructable(e, false)) return true;
    return policy_ == DefinitionPolicy::PolynomialInLinearPositions &&
           isReconstructable(e, true) && hasOnlyLinearUses(name);
}

bool SolveEqs::hasOnlyLinearUses(const std::string& name) {
    struct Frame { ExprId e; bool nonlinear; };
    std::vector<Frame> stack;
    for (const auto& conjunct : conjuncts_) stack.push_back({conjunct.second, false});
    std::unordered_map<ExprId, unsigned char> seen;
    while (!stack.empty()) {
        if (++substWork_ > workBudget_) return false;
        const auto frame = stack.back();
        stack.pop_back();
        const unsigned char context = frame.nonlinear ? 2 : 1;
        auto& contexts = seen[frame.e];
        if (contexts & context) continue;
        contexts |= context;
        const auto node = ir_.get(frame.e);
        if (node.kind == Kind::Variable && frame.nonlinear) {
            if (const auto* n = std::get_if<std::string>(&node.payload.value); n && *n == name)
                return false;
        }
        bool nonlinear = frame.nonlinear;
        switch (node.kind) {
            case Kind::ConstInt: case Kind::ConstReal: case Kind::Variable:
            case Kind::Add: case Kind::Sub: case Kind::Neg: case Kind::ToReal:
            case Kind::Eq: case Kind::Distinct: case Kind::Lt: case Kind::Leq:
            case Kind::Gt: case Kind::Geq: case Kind::And: case Kind::Or:
            case Kind::Not: case Kind::Implies: case Kind::Ite:
                break;
            case Kind::Mul: {
                unsigned nonConstants = 0;
                for (ExprId child : node.children) {
                    const auto kind = ir_.get(child).kind;
                    if (kind != Kind::ConstInt && kind != Kind::ConstReal) ++nonConstants;
                }
                nonlinear |= nonConstants > 1;
                break;
            }
            default: nonlinear = true; break;
        }
        for (ExprId child : node.children) stack.push_back({child, nonlinear});
    }
    return true;
}

ExprId SolveEqs::substitute(ExprId root, const std::string& name, ExprId replacement) {
    if (auto it = substMemo_.find(root); it != substMemo_.end()) return it->second;

    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        ++substWork_;   // bound total substitution work (see run()'s budget guard)
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (substMemo_.find(e) != substMemo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: ir_.addShared() may relocate exprs_

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
            TermExpr fresh{node.kind, node.sort, std::move(newChildren), node.payload};
            substMemo_[e] = ir_.addShared(std::move(fresh));
        }
    }
    return substMemo_.at(root);
}

void SolveEqs::computeUnsafeVars() {
    unsafeVars_.clear();
    struct F { ExprId e; bool underUF; };
    std::unordered_map<ExprId, unsigned char> seen;
    for (const auto& [level, root] : conjuncts_) {
        (void)level;
        std::vector<F> stack{{root, false}};
        while (!stack.empty()) {
            F f = stack.back();
            stack.pop_back();
            const unsigned char context = f.underUF ? 2 : 1;
            auto& contexts = seen[f.e];
            if (contexts & context) continue;
            contexts |= context;
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
        std::unordered_set<ExprId> seen;
        while (!flat.empty()) {
            ExprId e = flat.back();
            flat.pop_back();
            if (!seen.insert(e).second) continue;
            const auto& node = ir_.get(e);
            if (node.kind == Kind::And) {
                for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i)
                    flat.push_back(node.children[i]);
            } else {
                conjuncts_.push_back({level, e});
            }
        }
    }

    // Densification measurement (XOLVER_PP_SOLVE_EQS_DIAG): total DAG node count
    // over all conjuncts. Compared start vs end to see how much elimination
    // grows the formula — the Option-C signal for whether general elimination
    // is densifying (UNSAT-harmful) vs shrinking (SAT-helpful).
    const bool diag = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_PP_SOLVE_EQS_DIAG");
    auto dagSize = [&]() -> uint64_t {
        std::unordered_set<ExprId> seen;
        std::vector<ExprId> st;
        for (const auto& cj : conjuncts_) st.push_back(cj.second);
        while (!st.empty()) {
            ExprId e = st.back(); st.pop_back();
            if (!seen.insert(e).second) continue;
            for (ExprId c : ir_.get(e).children) st.push_back(c);
        }
        return seen.size();
    };
    const uint64_t dag0 = diag ? dagSize() : 0;

    // Variables feeding an uninterpreted-function/array argument are shared
    // terms in Nelson-Oppen combination; eliminating them is unsound. Pin them.
    computeUnsafeVars();

    bool progress = true;
    while (progress) {
        // Substitution-work budget. run() re-substitutes across ALL conjuncts
        // after EVERY elimination, so the pass is O(eliminations × formula-size).
        // On small formulas (e.g. QF_LIA convert) this is cheap, but on large
        // chained-equality systems (SMPT/nec Petri-nets: thousands of `aᵢ = Σx`
        // aux-defs over tens of thousands of conjuncts) it explodes into
        // billions of node-visits and burns the whole solve budget in
        // preprocessing — turning fast UNSATs into timeouts. When the work cap
        // is hit we stop eliminating and proceed with what we have: every
        // elimination performed so far is independently equisatisfiable and
        // registered for model replay, so a partial pass is SOUND (it is not a
        // verdict, only a simplification). Budget is generous enough to complete
        // the small formulas the pass actually helps; env-overridable for tuning.
        if (substWork_ > workBudget_) {
            if (eliminated_ > 0 && xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_PP_SOLVE_EQS_DIAG"))
                std::fprintf(stderr, "[SolveEqs] work budget hit after %zu elims; stopping\n",
                             eliminated_);
            break;
        }
        progress = false;
        for (size_t idx = 0; idx < conjuncts_.size(); ++idx) {
            ExprId c = conjuncts_[idx].second;
            const auto& node = ir_.get(c);
            if (node.kind != Kind::Eq || node.children.size() != 2) continue;
            ExprId lhs = node.children[0], rhs = node.children[1];

            std::string varName;
            ExprId defExpr = NullExpr;
            SortId varSort = NullSort;
            if (auto n = asNumericVar(lhs); n && !occurs(*n, rhs) && admissibleDefinition(*n, rhs)) {
                varName = *n; defExpr = rhs; varSort = ir_.get(lhs).sort;
            } else if (auto n2 = asNumericVar(rhs); n2 && !occurs(*n2, lhs) && admissibleDefinition(*n2, lhs)) {
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
    if (diag) {
        const uint64_t dag1 = dagSize();
        std::fprintf(stderr, "[SolveEqs] elim=%zu dag %llu->%llu ratio=%.2f work=%llu\n",
                     eliminated_, (unsigned long long)dag0, (unsigned long long)dag1,
                     dag0 ? (double)dag1 / (double)dag0 : 0.0,
                     (unsigned long long)substWork_);
    }
    return eliminated_ > 0;
}

void SolveEqs::commit() {
    if (eliminated_ == 0) return;
    auto replacement = conjuncts_;
    ir_.restoreAssertions(std::move(replacement));
}

} // namespace xolver
