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

ExprId UnconstrainedElim::mkSub(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Sub;
    e.sort = ir_.get(a).sort;
    e.children = {a, b};
    return ir_.addShared(std::move(e));
}

ExprId UnconstrainedElim::mkNeg(ExprId a) {
    CoreExpr e;
    e.kind = Kind::Neg;
    e.sort = ir_.get(a).sort;
    e.children = {a};
    return ir_.addShared(std::move(e));
}

std::optional<std::pair<std::string, ExprId>>
UnconstrainedElim::asValueUncTerm(ExprId e, ExprId target) {
    const auto& node = ir_.get(e);

    // Restrict to Int sort for now (LCTES target). Real would need extra
    // care for Mul-by-constant (rational division).
    if (node.sort != intSortId_) return std::nullopt;

    auto asConstInt = [&](ExprId x, mpz_class& out) -> bool {
        const auto& cn = ir_.get(x);
        if (cn.kind != Kind::ConstInt) return false;
        if (auto* iv = std::get_if<int64_t>(&cn.payload.value)) { out = *iv; return true; }
        if (auto* sv = std::get_if<std::string>(&cn.payload.value)) {
            try { out = mpz_class(*sv); return true; } catch (...) { return false; }
        }
        return false;
    };

    // Base case: Variable with occ==1.
    if (node.kind == Kind::Variable) {
        auto nm = asNumericVar(e);
        if (!nm) return std::nullopt;
        if (occ_.count(*nm) == 0 || occ_.at(*nm) != 1) return std::nullopt;
        if (unsafe_.count(*nm)) return std::nullopt;
        return std::make_pair(*nm, target);
    }

    // (- v) (unary negation): v := -target.
    if (node.kind == Kind::Neg && node.children.size() == 1) {
        const auto& cn = ir_.get(node.children[0]);
        if (cn.kind == Kind::Variable) {
            auto nm = asNumericVar(node.children[0]);
            if (!nm) return std::nullopt;
            if (occ_.count(*nm) == 0 || occ_.at(*nm) != 1) return std::nullopt;
            if (unsafe_.count(*nm)) return std::nullopt;
            return std::make_pair(*nm, mkNeg(target));
        }
        return std::nullopt;
    }

    // (+ a b ...): exactly one child is an unc-Variable (occ==1),
    // the others sum together; v := target - (others).
    if (node.kind == Kind::Add && node.children.size() >= 2) {
        int uncIdx = -1;
        std::string uncName;
        for (size_t i = 0; i < node.children.size(); ++i) {
            const auto& cn = ir_.get(node.children[i]);
            if (cn.kind != Kind::Variable) continue;
            auto nm = asNumericVar(node.children[i]);
            if (!nm) continue;
            if (occ_.count(*nm) == 0 || occ_.at(*nm) != 1) continue;
            if (unsafe_.count(*nm)) continue;
            // Sort must match parent's sort.
            if (ir_.get(node.children[i]).sort != intSortId_) continue;
            if (uncIdx != -1) return std::nullopt;  // 2+ unc vars → ambiguous
            uncIdx = static_cast<int>(i);
            uncName = *nm;
        }
        if (uncIdx == -1) return std::nullopt;
        // newTarget = target - sum(others)
        ExprId newTarget = target;
        for (size_t i = 0; i < node.children.size(); ++i) {
            if (static_cast<int>(i) == uncIdx) continue;
            newTarget = mkSub(newTarget, node.children[i]);
        }
        return std::make_pair(uncName, newTarget);
    }

    // (- a b): binary subtract. Two shapes:
    //   (- v X) → v := target + X
    //   (- X v) → v := X - target
    if (node.kind == Kind::Sub && node.children.size() == 2) {
        ExprId a = node.children[0], b = node.children[1];
        const auto& an = ir_.get(a);
        const auto& bn = ir_.get(b);
        if (an.kind == Kind::Variable) {
            auto nm = asNumericVar(a);
            if (nm && occ_.count(*nm) && occ_.at(*nm) == 1 &&
                !unsafe_.count(*nm) && ir_.get(a).sort == intSortId_) {
                CoreExpr addExpr;
                addExpr.kind = Kind::Add;
                addExpr.sort = intSortId_;
                addExpr.children = {target, b};
                ExprId newTarget = ir_.addShared(std::move(addExpr));
                return std::make_pair(*nm, newTarget);
            }
        }
        if (bn.kind == Kind::Variable) {
            auto nm = asNumericVar(b);
            if (nm && occ_.count(*nm) && occ_.at(*nm) == 1 &&
                !unsafe_.count(*nm) && ir_.get(b).sort == intSortId_) {
                return std::make_pair(*nm, mkSub(a, target));
            }
        }
        return std::nullopt;
    }

    // (* k v) or (* v k): coefficient ±1 only (Int bijectivity).
    if (node.kind == Kind::Mul && node.children.size() == 2) {
        ExprId a = node.children[0], b = node.children[1];
        mpz_class kVal;
        ExprId varE = NullExpr;
        if (asConstInt(a, kVal)) varE = b;
        else if (asConstInt(b, kVal)) varE = a;
        else return std::nullopt;
        if (kVal != 1 && kVal != -1) return std::nullopt;
        const auto& vn = ir_.get(varE);
        if (vn.kind != Kind::Variable) return std::nullopt;
        auto nm = asNumericVar(varE);
        if (!nm) return std::nullopt;
        if (occ_.count(*nm) == 0 || occ_.at(*nm) != 1) return std::nullopt;
        if (unsafe_.count(*nm)) return std::nullopt;
        ExprId newTarget = (kVal == 1) ? target : mkNeg(target);
        return std::make_pair(*nm, newTarget);
    }

    return std::nullopt;
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
    // Iterative DFS over Boolean structure. Each worklist entry is an
    // (ExprId, target) pair meaning "find a witness that makes this expr
    // evaluate to `target`". When we hit an atom-level node we delegate
    // to tryAtomDrop; first success exits the loop. Heap-allocated to
    // survive arbitrary structural depth (e.g. 60k-deep `(or A (or A ...))`).
    std::vector<std::pair<ExprId, bool>> worklist;
    worklist.reserve(16);
    worklist.emplace_back(e, target);

    while (!worklist.empty()) {
        auto [cur, curTarget] = worklist.back();
        worklist.pop_back();
        const auto& node = ir_.get(cur);

        if (node.kind == Kind::Not) {
            if (node.children.size() != 1) continue;
            worklist.emplace_back(node.children[0], !curTarget);
            continue;
        }
        if (node.kind == Kind::Or) {
            // target=true monotone: any disjunct true suffices.
            if (!curTarget) continue;
            // Push in REVERSE so the leftmost is processed first (matches
            // the previous recursive left-to-right search order).
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                worklist.emplace_back(node.children[i], true);
            }
            continue;
        }
        if (node.kind == Kind::And) {
            // target=false monotone: any conjunct false suffices.
            if (curTarget) continue;
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                worklist.emplace_back(node.children[i], false);
            }
            continue;
        }
        if (node.kind == Kind::Implies) {
            // (=> A B) target=true ≡ (or (not A) B). Push B first so A
            // (the equivalent "not A" check at target=false) is checked
            // first under the LIFO stack.
            if (node.children.size() != 2 || !curTarget) continue;
            worklist.emplace_back(node.children[1], true);
            worklist.emplace_back(node.children[0], false);
            continue;
        }

        // Atom-level: delegate.
        if (tryAtomDrop(cur, curTarget, out)) return true;
    }
    return false;
}

bool UnconstrainedElim::tryAtomDrop(ExprId e, bool target, DropAction& out) const {
    const auto& node = ir_.get(e);

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

    // Phase: try direct Variable (existing behavior, ALL relations).
    if (auto n = asNumericVar(lhs)) {
        varName = *n; bound = rhs; xIsLeft = true;
    } else if (auto n2 = asNumericVar(rhs)) {
        varName = *n2; bound = lhs; xIsLeft = false;
    } else if (isEq) {
        // Sort-safety check: if v is Int and the other side has Real sort
        // (e.g. division `(/ 1 2)`), the equality is intrinsically constrained
        // and may have NO integer solution. Dropping would unsoundly turn
        // unsat into sat. Require identical sort.
        SortId lhsSort = ir_.get(lhs).sort;
        SortId rhsSort = ir_.get(rhs).sort;
        if (lhsSort != rhsSort) return false;
        // Phase 2 — TERM-level unc for EQUALITY only. Other relations need
        // monotone analysis (e.g. (< (+ v 5) t)  ⇒ v < t - 5) which we keep
        // simple here. For Eq the inverse term IS the new witness, no
        // monotonicity concern.
        auto lhsTerm = const_cast<UnconstrainedElim*>(this)->asValueUncTerm(lhs, rhs);
        if (lhsTerm) { varName = lhsTerm->first; bound = lhsTerm->second; xIsLeft = true; }
        else {
            auto rhsTerm = const_cast<UnconstrainedElim*>(this)->asValueUncTerm(rhs, lhs);
            if (rhsTerm) { varName = rhsTerm->first; bound = rhsTerm->second; xIsLeft = false; }
            else return false;
        }
    } else {
        return false;
    }

    if (occ_.count(varName) == 0 || occ_.at(varName) != 1) return false;
    if (unsafe_.count(varName)) return false;
    // Defensive: ensure the var truly does not appear in `bound`. (Should be
    // implied by occ==1 since the only occurrence is the var-side, but the
    // count is structural — a shared DAG node could double-count us. For
    // term-level Eq, `bound` is a freshly-constructed inverse — it does not
    // textually contain varName since the unc-term construction only mixes
    // the *other* children of the parent into the new bound.)
    if (varOccursIn(varName, bound)) return false;

    // Sort: for term-level unc, derive from the var's own sort (not from
    // lhs/rhs which may now be a synthesized expression).
    SortId sort = intSortId_;  // term-level path forces Int sort above
    if (auto n = asNumericVar(lhs)) sort = ir_.get(lhs).sort;
    else if (auto n2 = asNumericVar(rhs)) sort = ir_.get(rhs).sort;
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
        // UncElim (permissive) — distinguishes from SolveEqs's strict Elim
        // so reconstruct can default free vars in the bound to 0 when those
        // vars were themselves dropped as unconstrained (see lra_024 chain
        // x1<x2<x3<x4 — every var is unc, defining terms reference each
        // other, and strict eval cycles back to nullopt).
        mc_.registerUncElimination(a.varName, a.sort, a.bound);
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
