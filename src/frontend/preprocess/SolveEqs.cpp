#include "frontend/preprocess/SolveEqs.h"
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "util/EnvParam.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <gmpxx.h>

namespace xolver {

SolveEqs::SolveEqs(CoreIr& ir, ModelConverter& mc)
    : ir_(ir), mc_(mc),
      boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()), realSortId_(ir.realSortId()) {
    {
        long long v = env::paramLong("XOLVER_PP_SOLVE_EQS_BUDGET",
                                     static_cast<long>(workBudget_));
        if (v > 0) workBudget_ = static_cast<uint64_t>(v);
    }
    {
        double v = env::paramDouble("XOLVER_PP_SOLVE_EQS_GROWTH_CAP", growthCap_);
        if (v > 0.0) growthCap_ = v;
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
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            fresh.children = std::move(newChildren);
            fresh.payload = node.payload;
            substMemo_[e] = ir_.addShared(std::move(fresh));
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

    // Densification measurement (XOLVER_PP_SOLVE_EQS_DIAG): total DAG node count
    // over all conjuncts. Compared start vs end to see how much elimination
    // grows the formula — the Option-C signal for whether general elimination
    // is densifying (UNSAT-harmful) vs shrinking (SAT-helpful).
    const bool diag = xolver::env::diag("XOLVER_PP_SOLVE_EQS_DIAG");
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
    // Densification guard (general ±1-pivot only). General elimination SHRINKS
    // the formula when it is genuinely simplifying (QF_LIA convert: ratio ~0.82)
    // but GROWS it when it fans a hub variable's definition into many
    // constraints (SMPT Petri-net Farkas systems, e.g. CircularTrains: ratio
    // ~1.9–2.2). A grown formula keeps SAT model-search cheap but obscures the
    // short UNSAT (Farkas) certificate, turning fast UNSATs into timeouts. So
    // when the live DAG exceeds the initial size by growthCap_, we stop doing
    // further general eliminations (bare-var elimination, which never densifies,
    // continues). Measured periodically — recomputing the DAG every elimination
    // would be quadratic. Only meaningful when general elimination is enabled.
    const uint64_t dag0 = (generalLinear_ || diag) ? dagSize() : 0;
    size_t lastGrowthCheck_ = 0;

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
            if (eliminated_ > 0 && std::getenv("XOLVER_PP_SOLVE_EQS_DIAG"))
                std::fprintf(stderr, "[SolveEqs] work budget hit after %zu elims; stopping\n",
                             eliminated_);
            break;
        }
        // Periodic densification check (general elimination only). Once the live
        // formula has grown past growthCap_×, further general eliminations are
        // fanning out hub variables (UNSAT-harmful); disable them. Bare-var
        // elimination continues (it never densifies). Checked every few
        // eliminations to keep the DAG recomputation off the hot path.
        if (generalLinear_ && !gaussDensifyAbort_ && dag0 > 0 &&
            eliminated_ >= lastGrowthCheck_ + kGrowthCheckEvery_) {
            lastGrowthCheck_ = eliminated_;
            if ((double)dagSize() > (double)dag0 * growthCap_) {
                gaussDensifyAbort_ = true;
                if (xolver::env::diag("XOLVER_PP_SOLVE_EQS_DIAG"))
                    std::fprintf(stderr, "[SolveEqs] densify cap hit after %zu elims; "
                                 "general elimination disabled\n", eliminated_);
            }
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
            if (auto n = asNumericVar(lhs); n && !occurs(*n, rhs) && isLinearReconstructable(rhs)) {
                varName = *n; defExpr = rhs; varSort = ir_.get(lhs).sort;
            } else if (auto n2 = asNumericVar(rhs); n2 && !occurs(*n2, lhs) && isLinearReconstructable(lhs)) {
                varName = *n2; defExpr = lhs; varSort = ir_.get(rhs).sort;
            } else {
                // Bare-variable path did not match. Try the general ±1-pivot
                // linear elimination on this equality (Farkas-style
                // `expr = expr`), which the bare-var form cannot reach.
                if (generalLinear_ && tryGeneralEliminate(idx)) {
                    progress = true;
                    break;  // indices shifted; restart scan
                }
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

bool SolveEqs::tryGeneralEliminate(size_t idx) {
    if (gaussDensifyAbort_) return false;   // densification cap reached
    ExprId c = conjuncts_[idx].second;

    // Parse the equality into a canonical linear form Σ coeffs[v]·v = rhs.
    // Returns false for anything nonlinear (e.g. the bilinear Farkas products
    // in QF_NIA SAT14) — those are correctly skipped.
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class rhs;
    Relation rel;
    if (!extractLinearConstraint(c, ir_, coeffs, rhs, rel)) return false;
    if (rel != Relation::Eq) return false;

    // Collect every variable's ExprId + sort from this equality's tree. The
    // replacement we build reuses these exact (hash-consed) variable nodes, so
    // we never need to reconstruct a Variable from its name (sort-agnostically).
    std::unordered_map<std::string, ExprId> varExpr;
    {
        std::vector<ExprId> stack{c};
        while (!stack.empty()) {
            ExprId e = stack.back();
            stack.pop_back();
            const auto& node = ir_.get(e);
            if (node.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&node.payload.value))
                    varExpr.emplace(*nm, e);
            }
            for (ExprId ch : node.children) stack.push_back(ch);
        }
    }

    // Deterministic order: sort variable names so pivot choice is reproducible
    // (unordered_map iteration order is not).
    std::vector<std::string> names;
    names.reserve(coeffs.size());
    for (const auto& kv : coeffs)
        if (kv.second != 0) names.push_back(kv.first);
    std::sort(names.begin(), names.end());

    // Helper: build a constant node of the given sort from an exact rational.
    // Mirrors FormulaRewriter::mkIntOrReal — refuses non-integer/oversized Int
    // literals (returns NullExpr) so we never emit an unsound or lossy constant.
    auto mkConst = [&](const mpq_class& v, SortId sort) -> ExprId {
        if (sort == realSortId_ && realSortId_ != NullSort) {
            CoreExpr e; e.kind = Kind::ConstReal; e.sort = sort;
            e.payload = Payload(v.get_str());
            return ir_.addShared(std::move(e));
        }
        if (sort == intSortId_ && intSortId_ != NullSort) {
            if (v.get_den() != 1) return NullExpr;
            mpz_class num = v.get_num();
            if (!num.fits_slong_p()) return NullExpr;
            CoreExpr e; e.kind = Kind::ConstInt; e.sort = sort;
            e.payload = Payload(static_cast<int64_t>(num.get_si()));
            return ir_.addShared(std::move(e));
        }
        return NullExpr;
    };

    // Try each ±1-coefficient variable as the pivot, in deterministic order,
    // and build its exact replacement. Use the first that succeeds.
    for (const std::string& pivot : names) {
        const mpq_class& cj = coeffs[pivot];
        if (cj != 1 && cj != -1) continue;          // need |coeff| == 1 (exact)
        if (unsafeVars_.count(pivot)) continue;     // UF/array shared (N-O)
        auto pit = varExpr.find(pivot);
        if (pit == varExpr.end()) continue;
        SortId sort = ir_.get(pit->second).sort;
        if (sort != intSortId_ && sort != realSortId_) continue;

        // All other variables must share the pivot's sort (avoid Int/Real mixing
        // through ToReal — keep the replacement homogeneous and reconstructable).
        bool sortOk = true;
        for (const std::string& v : names) {
            if (v == pivot) continue;
            auto vit = varExpr.find(v);
            if (vit == varExpr.end() || ir_.get(vit->second).sort != sort) { sortOk = false; break; }
        }
        if (!sortOk) continue;

        // xⱼ = (rhs − Σᵢ≠ⱼ aᵢ·xᵢ) / cⱼ, with cⱼ = ±1:
        //   cⱼ = +1 →  xⱼ = Σᵢ≠ⱼ (−aᵢ)·xᵢ + rhs
        //   cⱼ = −1 →  xⱼ = Σᵢ≠ⱼ ( aᵢ)·xᵢ − rhs
        const bool pivotPos = (cj == 1);
        SmallVector<ExprId, 4> terms;
        bool buildOk = true;
        for (const std::string& v : names) {
            if (v == pivot) continue;
            mpq_class tc = pivotPos ? -coeffs[v] : coeffs[v];
            if (tc == 0) continue;
            ExprId vexpr = varExpr[v];
            ExprId term;
            if (tc == 1) {
                term = vexpr;
            } else if (tc == -1) {
                CoreExpr neg; neg.kind = Kind::Neg; neg.sort = sort;
                neg.children.push_back(vexpr);
                term = ir_.addShared(std::move(neg));
            } else {
                ExprId kc = mkConst(tc, sort);
                if (kc == NullExpr) { buildOk = false; break; }
                CoreExpr mul; mul.kind = Kind::Mul; mul.sort = sort;
                mul.children.push_back(kc);
                mul.children.push_back(vexpr);
                term = ir_.addShared(std::move(mul));
            }
            terms.push_back(term);
        }
        if (!buildOk) continue;

        mpq_class constTerm = pivotPos ? rhs : -rhs;
        ExprId replacement;
        if (terms.empty()) {
            replacement = mkConst(constTerm, sort);
            if (replacement == NullExpr) continue;
        } else {
            if (constTerm != 0) {
                ExprId kc = mkConst(constTerm, sort);
                if (kc == NullExpr) continue;
                terms.push_back(kc);
            }
            if (terms.size() == 1) {
                replacement = terms[0];
            } else {
                CoreExpr add; add.kind = Kind::Add; add.sort = sort;
                add.children = terms;
                replacement = ir_.addShared(std::move(add));
            }
        }

        // Eliminate: drop this equality, substitute pivot ↦ replacement
        // everywhere else, and record the (exact, linear) definition for model
        // replay. The pivot cannot occur in `replacement` (it was excluded), so
        // no self-reference is created.
        conjuncts_.erase(conjuncts_.begin() + static_cast<long>(idx));
        substMemo_.clear();
        for (auto& cj2 : conjuncts_) cj2.second = substitute(cj2.second, pivot, replacement);
        mc_.registerElimination(pivot, sort, replacement);
        ++eliminated_;
        return true;
    }
    return false;
}

void SolveEqs::commit() {
    if (eliminated_ == 0) return;
    ir_.clearAssertions();
    for (const auto& [level, e] : conjuncts_) ir_.addAssertion(e, level);
}

} // namespace xolver
