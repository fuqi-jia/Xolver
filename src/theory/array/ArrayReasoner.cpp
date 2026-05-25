#include "theory/array/ArrayReasoner.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "expr/ir.h"
#include <cassert>

namespace nlcolver {

void ArrayReasoner::reset() {
    selectTerms_.clear();
    storeTerms_.clear();
    constArrayTerms_.clear();
    selectSet_.clear();
    storeSet_.clear();
    constArraySet_.clear();
    nextTermToScan_ = 0;
    row2Done_.clear();
    extDone_.clear();
}

ExprId ArrayReasoner::originExpr(EufTermId t) const {
    if (t == NullEufTerm) return NullExpr;
    return tm_->node(t).origin;
}

bool ArrayReasoner::symIsSelect(EufTermId t) const {
    return tm_->symbolName(tm_->node(t).symbol) == "#array.select";
}
bool ArrayReasoner::symIsStore(EufTermId t) const {
    return tm_->symbolName(tm_->node(t).symbol) == "#array.store";
}
bool ArrayReasoner::symIsConstArray(EufTermId t) const {
    return tm_->symbolName(tm_->node(t).symbol) == "#array.const";
}

bool ArrayReasoner::discoverArrayTerms() {
    if (!active()) return false;
    bool found = false;
    EufTermId total = static_cast<EufTermId>(tm_->termCount());
    for (EufTermId t = nextTermToScan_; t < total; ++t) {
        const auto& n = tm_->node(t);
        if (n.args.empty()) continue;
        if (symIsSelect(t)) {
            if (selectSet_.insert(t).second) { selectTerms_.push_back(t); found = true; }
        } else if (symIsStore(t)) {
            if (storeSet_.insert(t).second) { storeTerms_.push_back(t); found = true; }
        } else if (symIsConstArray(t)) {
            if (constArraySet_.insert(t).second) { constArrayTerms_.push_back(t); found = true; }
        }
    }
    nextTermToScan_ = total;
    return found;
}

EufTermId ArrayReasoner::internSelect(ExprId arrayExpr, ExprId indexExpr,
                                      std::deque<PendingMerge>& outQueue) {
    if (arrayExpr == NullExpr || indexExpr == NullExpr) return NullEufTerm;
    CoreIr& ir = const_cast<CoreIr&>(*ir_);
    const auto& arrNode = ir.get(arrayExpr);
    // Element sort of the array.
    SortId elemSort = NullSort;
    if (auto params = ir.arraySortParams(arrNode.sort)) {
        elemSort = params->second;
    }
    // Build a Select CoreExpr (CoreIr is not hash-consed; rely on EUF term
    // manager dedup to share structurally-equal selects).
    CoreExpr sel;
    sel.kind = Kind::Select;
    sel.sort = elemSort;
    sel.children.push_back(arrayExpr);
    sel.children.push_back(indexExpr);
    ExprId selExpr = ir.add(std::move(sel));

    EufTermId t = tm_->intern(selExpr, ir);
    if (t != NullEufTerm) {
        egraph_->ensureTermRegistered(t, outQueue);
        // Keep our registry in sync immediately so the new select participates
        // in Const/Row2 reasoning on this very check().
        if (symIsSelect(t) && selectSet_.insert(t).second) {
            selectTerms_.push_back(t);
        }
    }
    return t;
}

void ArrayReasoner::enqueueEagerMerges(std::deque<PendingMerge>& outQueue) {
    if (!active()) return;
    discoverArrayTerms();

    // --- Row1: select(store(a,i,v),i) = v ---------------------------------
    // For each store term s=store(a,i,v): intern select(s,i) and merge with v.
    // We iterate by index because internSelect may append to selectTerms_.
    size_t nStores = storeTerms_.size();
    for (size_t si = 0; si < nStores; ++si) {
        EufTermId s = storeTerms_[si];
        const auto& sn = tm_->node(s);
        if (sn.args.size() != 3) continue;
        EufTermId iTerm = sn.args[1];
        EufTermId vTerm = sn.args[2];
        ExprId sExpr = originExpr(s);
        ExprId iExpr = originExpr(iTerm);
        if (sExpr == NullExpr || iExpr == NullExpr) continue;
        EufTermId selSI = internSelect(sExpr, iExpr, outQueue);
        if (selSI == NullEufTerm) continue;
        if (!egraph_->same(selSI, vTerm)) {
            MergeReason mr;
            mr.kind = MergeReasonKind::ArrayRow1;
            mr.lit = SatLit();
            outQueue.push_back({selSI, vTerm, mr});
        }
    }

    // --- Const: select(const(v),i) = v ------------------------------------
    // For each select term sel=select(c,j): if c's class contains a const(v),
    // merge sel with v.
    size_t nSelects = selectTerms_.size();
    for (size_t k = 0; k < nSelects; ++k) {
        EufTermId sel = selectTerms_[k];
        const auto& seln = tm_->node(sel);
        if (seln.args.size() != 2) continue;
        EufTermId arrTerm = seln.args[0];
        EClassId arrClass = egraph_->rep(arrTerm);
        for (EufTermId member : egraph_->classMembers(arrClass)) {
            if (!symIsConstArray(member)) continue;
            const auto& cn = tm_->node(member);
            if (cn.args.size() != 1) continue;
            EufTermId vTerm = cn.args[0];
            if (!egraph_->same(sel, vTerm)) {
                MergeReason mr;
                mr.kind = MergeReasonKind::ArrayConst;
                mr.lit = SatLit();
                outQueue.push_back({sel, vTerm, mr});
            }
            break;  // one const witness per class suffices
        }
    }
}

std::optional<std::vector<SatLit>>
ArrayReasoner::instantiateLemma(const std::vector<ArrayDiseq>& disequalities) {
    if (!active() || !registry_) return std::nullopt;
    discoverArrayTerms();

    // --- Row2: i!=j => select(store(a,i,v),j) = select(a,j) ---------------
    // Trigger: a select term select(s, j) where s (or its class) is a store
    // store(a,i,v). Emit lemma  (i=j) OR (select(store...,j) = select(a,j)).
    // We need a SAT split because the antecedent i!=j is not decided yet.
    size_t nSelects = selectTerms_.size();
    for (size_t k = 0; k < nSelects; ++k) {
        EufTermId selTerm = selectTerms_[k];
        const auto& seln = tm_->node(selTerm);
        if (seln.args.size() != 2) continue;
        EufTermId arrArg = seln.args[0];
        EufTermId jTerm = seln.args[1];

        // Find a store in arrArg's class.
        EClassId arrClass = egraph_->rep(arrArg);
        for (EufTermId member : egraph_->classMembers(arrClass)) {
            if (!symIsStore(member)) continue;
            const auto& stn = tm_->node(member);
            if (stn.args.size() != 3) continue;
            EufTermId aTerm = stn.args[0];   // underlying array
            EufTermId iTerm = stn.args[1];   // write index
            // (skip vTerm = stn.args[2])

            // If i and j are already known equal, Row1/Const(/congruence)
            // handles it; skip the case split. If known distinct, the
            // fall-through equality is forced — still emit the lemma so the
            // SAT solver records select(store,j)=select(a,j). Dedup by stable
            // term ids (store member id, read index j id).
            uint64_t key = pairKey(member, jTerm);
            if (!row2Done_.insert(key).second) continue;

            ExprId iExpr = originExpr(iTerm);
            ExprId jExpr = originExpr(jTerm);
            ExprId aExpr = originExpr(aTerm);
            ExprId selStoreExpr = originExpr(selTerm);  // select(store(...),j)
            if (iExpr == NullExpr || jExpr == NullExpr ||
                aExpr == NullExpr || selStoreExpr == NullExpr) {
                continue;
            }

            // Build select(a, j) term.
            std::deque<PendingMerge> dummy;  // ensureTermRegistered side queue
            EufTermId selAJ = internSelect(aExpr, jExpr, dummy);
            // (the discovered congruence merges in `dummy` are harmless to
            //  drop: they will be re-derived in the next saturation pass once
            //  these terms are registered; ensureTermRegistered already wired
            //  them into the signature table.)
            if (selAJ == NullEufTerm) continue;
            ExprId selAJExpr = originExpr(selAJ);
            if (selAJExpr == NullExpr) continue;

            // Lemma:  (i=j)  OR  (select(store(a,i,v),j) = select(a,j))
            SatLit ijEq = registry_->getOrCreateEufEqualityAtom(iExpr, jExpr);
            SatLit readEq = registry_->getOrCreateEufEqualityAtom(selStoreExpr, selAJExpr);
            return std::vector<SatLit>{ijEq, readEq};
        }
    }

    // --- Extensionality: a!=b => select(a,k) != select(b,k), fresh k ------
    for (const auto& d : disequalities) {
        EufTermId aTerm = d.lhs;
        EufTermId bTerm = d.rhs;
        // Only array-sorted disequalities.
        const auto& an = tm_->node(aTerm);
        if (!ir_->arraySortParams(an.sort)) continue;

        uint64_t lo = aTerm < bTerm ? aTerm : bTerm;
        uint64_t hi = aTerm < bTerm ? bTerm : aTerm;
        uint64_t key = pairKey(static_cast<uint32_t>(lo), static_cast<uint32_t>(hi));
        if (!extDone_.insert(key).second) continue;

        ExprId aExpr = originExpr(aTerm);
        ExprId bExpr = originExpr(bTerm);
        if (aExpr == NullExpr || bExpr == NullExpr) continue;

        // Fresh witness index k of the array's index sort.
        CoreIr& ir = const_cast<CoreIr&>(*ir_);
        SortId idxSort = NullSort;
        if (auto params = ir.arraySortParams(an.sort)) idxSort = params->first;
        ExprId kExpr = ir.makeFreshVariable(idxSort, "__nlc_ext_idx");

        std::deque<PendingMerge> dummy;
        EufTermId selAK = internSelect(aExpr, kExpr, dummy);
        EufTermId selBK = internSelect(bExpr, kExpr, dummy);
        if (selAK == NullEufTerm || selBK == NullEufTerm) continue;
        ExprId selAKExpr = originExpr(selAK);
        ExprId selBKExpr = originExpr(selBK);
        if (selAKExpr == NullExpr || selBKExpr == NullExpr) continue;

        // Lemma:  (a=b)  OR  (select(a,k) != select(b,k))
        SatLit abEq = registry_->getOrCreateEufEqualityAtom(aExpr, bExpr);
        SatLit readEq = registry_->getOrCreateEufEqualityAtom(selAKExpr, selBKExpr);
        return std::vector<SatLit>{abEq, readEq.negated()};
    }

    return std::nullopt;
}

} // namespace nlcolver
