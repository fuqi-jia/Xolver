#include "theory/array/ArrayReasoner.h"
#include "util/EnvParam.h"
#include "theory/array/AniaProfile.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include "expr/ir.h"
#include "util/MpqUtils.h"
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <string>

namespace xolver {

ArrayReasoner::ArrayReasoner() {
    row2ConstEnabled_ = xolver::env::diag("XOLVER_AX_ROW2_CONST");
    // L1: relevancy-driven completion (default-OFF). See header.
    lazyComplete_ = xolver::env::diag("XOLVER_AX_LAZY");
    // L2: eager Row2 merge on known diseqs (default-OFF). See header.
    row2DiseqEnabled_ = xolver::env::diag("XOLVER_AX_ROW2_DISEQ");
    // Default ON (soundness: read2/read5 class); explicit opt-out for A/B.
    selectCompletionEnabled_ = !xolver::env::diag("XOLVER_AX_NO_SELECT_COMPLETE");
    // PROMOTED default-ON (was opt-in XOLVER_AX_EXT_WITNESS_COMPLETE). Phase A
    // (agent-array-deep, 2026-05-31) measured: fanning the fresh Ext witness k
    // through store towers recovers ALL 38 QF_AX storeinv cases (18 sat + 20
    // unsat) to the correct verdict, 0 unsound, regression 668/668 OFF+ON, and
    // the feared storecomm genuine-sat regression did NOT reproduce (159
    // already-solved storecomm cases stable). Explicit opt-out for A/B baseline.
    extWitnessComplete_ = !xolver::env::diag("XOLVER_AX_NO_EXT_WITNESS_COMPLETE");
    // XOLVER_AX_COMPLETE_BUDGET (default 0 = unbounded): cap the TOTAL number of
    // read-over-write completion selects interned across the whole solve. The
    // driver-verification QF_ANIA/QF_AUFNIA family (cdaudio/floppy/kbfiltr/…)
    // has ~100 arrays × ~600 read indices, so unbounded completion interns tens
    // of thousands of select terms (40-87% of the solve wall — agent-array-deep
    // B2-alt profiling) and the case times out. completeStoreSelects only adds
    // TAUTOLOGICAL selects, and any genuinely-missed read-over-write instance is
    // caught by the arrayModelDefinitelyViolates floor (sat→unknown, never a
    // wrong verdict). So capping is verdict-SOUND: it can only lose completeness
    // (a borderline case floors to unknown), and it RECOVERS the many driver
    // sats whose completion was largely wasteful (independent arrays) by letting
    // the solver reach a consistent model the floor then validates.
    {
        long v = env::paramLong("XOLVER_AX_COMPLETE_BUDGET",
                                static_cast<long>(completeBudget_));
        if (v > 0) completeBudget_ = static_cast<size_t>(v);
    }
}

std::optional<std::string> ArrayReasoner::constToken(EufTermId t) const {
    ExprId e = originExpr(t);
    if (e == NullExpr || !ir_) return std::nullopt;
    const auto& expr = ir_->get(e);
    const auto& v = expr.payload.value;
    // SOUNDNESS: the token must satisfy "distinct tokens ⇒ distinct VALUES".
    // String equality is NOT value equality for numerics: ConstInt/ConstReal
    // payloads are stored as raw parser text (adapter.cpp), so "1", "1.0" and
    // "2/2" are the same value but different strings. We therefore CANONICALIZE
    // numeric literals to a reduced rational before tokenizing. Uninterpreted
    // constants are Kind::Variable (not handled here) ⇒ nullopt: two distinct
    // uninterpreted names do NOT imply distinct values. ConstBV/ConstFP are out
    // of the validated scope and have no guaranteed canonical form ⇒ nullopt,
    // so Row2 falls back to the complete SAT-split lemma.
    switch (expr.kind) {
        case Kind::ConstBool:
            if (auto* b = std::get_if<bool>(&v)) return std::string("b:") + (*b ? "1" : "0");
            return std::nullopt;
        case Kind::ConstInt:
        case Kind::ConstReal: {
            try {
                mpq_class q;
                if (auto* i = std::get_if<int64_t>(&v)) q = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&v)) q = mpqFromString(*s);
                else return std::nullopt;
                q.canonicalize();   // "2/2" -> "1", reduce num/den
                return "n:" + q.get_str();
            } catch (...) {
                return std::nullopt;  // unparseable ⇒ do not claim distinctness
            }
        }
        default:
            return std::nullopt;
    }
}

bool ArrayReasoner::provablyDistinctConstIndices(EufTermId i, EufTermId j) const {
    auto ti = constToken(i);
    if (!ti) return false;
    auto tj = constToken(j);
    if (!tj) return false;
    return *ti != *tj;
}

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
    selectCompleteDone_.clear();
    completeInternsDone_ = 0;
    extWitnessIdx_.clear();
    extWitnessIdxTerms_.clear();
    internalSelect_.clear();
    completeLastSelectScanEnd_ = 0;
    completeLastTermScanEnd_ = 0;
    completeArrayCache_.clear();
    completeReadIdxCache_.clear();
    completeReadIdxSeen_.clear();
}

ExprId ArrayReasoner::originExpr(EufTermId t) const {
    if (t == NullEufTerm) return NullExpr;
    return tm_->node(t).origin;
}

SatLit ArrayReasoner::makeRow2IndexEqLit(ExprId iExpr, ExprId jExpr) {
    // Combination path: if BOTH indices are registered shared (arith) terms,
    // the (i=j) antecedent must be a shared-equality atom so that an arith
    // fact (e.g. i = j+0 deduced by LIA/LRA) and the Row2 case split refer to
    // the SAME SAT literal. Routing it through getOrCreateEufEqualityAtom
    // would create an EUF-only literal disconnected from arith's notion of
    // i=j, making the lemma incomplete (and, combined with the bridge,
    // potentially unsound). See CRITICAL soundness point #1.
    if (sharedTermRegistry_) {
        auto sa = sharedTermRegistry_->findByExprId(iExpr);
        auto sb = sharedTermRegistry_->findByExprId(jExpr);
        if (sa && sb) {
            return registry_->getOrCreateSharedEqualityAtom(*sa, *sb);
        }
    }
    // Pure QF_AX (uninterpreted indices) or one side not shared: EUF equality.
    return registry_->getOrCreateEufEqualityAtom(iExpr, jExpr);
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
    // Centralized saturation cap: ALL synthesized selects (Row1/Row2/extensional/
    // completion) flow through internSelect, so capping here bounds the entire
    // array-axiom saturation uniformly. Previously only completeStoreSelects
    // counted against completeBudget_, leaving Row1/Row2/ext UNCAPPED — on a deep
    // store-tower equality (e.g. GrandProduct) those saturation passes can fail to
    // reach fixpoint and diverge. With completeBudget_==0 (default) this is a
    // no-op (unlimited, no behaviour change); a finite XOLVER_AX_COMPLETE_BUDGET
    // forces termination (the resulting model is re-validated, invariant 1).
    if (completeBudget_ != 0 && completeInternsDone_ >= completeBudget_)
        return NullEufTerm;
    CoreIr& ir = const_cast<CoreIr&>(*ir_);
    const auto& arrNode = ir.get(arrayExpr);
    // Element sort of the array.
    SortId elemSort = NullSort;
    if (auto params = ir.arraySortParams(arrNode.sort)) {
        elemSort = params->second;
    }
    // Build a Select CoreExpr. As of iter-62, CoreIr exposes addShared()
    // which hash-cons-dedups identical (kind, sort, children, payload)
    // tuples. Structurally-equal selects (same array + same index)
    // collapse to the same ExprId BEFORE the EUF term manager interns
    // them, sharing earlier in the pipeline.
    CoreExpr sel;
    sel.kind = Kind::Select;
    sel.sort = elemSort;
    sel.children.push_back(arrayExpr);
    sel.children.push_back(indexExpr);
    ExprId selExpr = ir.addShared(std::move(sel));

    EufTermId t = tm_->intern(selExpr, ir);
    if (t != NullEufTerm) {
        egraph_->ensureTermRegistered(t, outQueue);
        // Mark as internally-synthesized (Row1/Row2/Ext/completion): its index is
        // NOT a genuine formula read index and must not seed completion.
        internalSelect_.insert(t);
        // Keep our registry in sync immediately so the new select participates
        // in Const/Row2 reasoning on this very check().
        if (symIsSelect(t) && selectSet_.insert(t).second) {
            selectTerms_.push_back(t);
            ++completeInternsDone_;  // count every synthesized select (cap above)
        }
    }
    return t;
}

void ArrayReasoner::collectIndexSharedTerms(std::unordered_set<SharedTermId>& out) const {
    if (!sharedTermRegistry_ || !tm_) return;
    auto addIdx = [&](EufTermId t) {
        const auto& n = tm_->node(t);
        if (n.args.size() < 2) return;
        ExprId idxExpr = originExpr(n.args[1]);   // arg[1] = index for select/store
        if (idxExpr == NullExpr) return;
        if (auto s = sharedTermRegistry_->findByExprId(idxExpr)) out.insert(*s);
    };
    for (EufTermId s : selectTerms_) addIdx(s);
    for (EufTermId s : storeTerms_)  addIdx(s);
}

void ArrayReasoner::collectValueSharedTerms(std::unordered_set<SharedTermId>& out) const {
    if (!sharedTermRegistry_ || !tm_) return;
    // The element/value side of array reasoning: the stored value (arg[2] of a
    // store) and the read result (a select term itself). Their deduced equalities
    // (e.g. select(store(a,i,v),j) ≡ another read, tying two stored values) must
    // reach arith — but a value-pair deduced equality first surfaces at STANDARD
    // effort where cb_propagate drops the lemma yet deducedEqCache_ records it,
    // permanently blocking Full-effort propagation. TheoryManager unions this set
    // with the index set to DEFER array value/index pairs to Full (alra_010:
    // store elements e0/e1/e0+3/e1+3 are exactly these arg[2] terms).
    auto addShared = [&](ExprId e) {
        if (e == NullExpr) return;
        if (auto s = sharedTermRegistry_->findByExprId(e)) out.insert(*s);
    };
    auto addTermShared = [&](EufTermId t) { addShared(originExpr(t)); };
    for (EufTermId s : storeTerms_) {
        const auto& n = tm_->node(s);
        if (n.args.size() >= 3) addTermShared(n.args[2]);  // stored value
    }
    // The READ RESULT of a select is, in combination, a fresh Purifier BRIDGE var
    // (`bridge = select(...)`) merged with the select term in the e-graph — NOT the
    // select expr itself. So collect the shared terms in the select's e-graph CLASS
    // (the bridge lands there via the unconditional definitional merge). Without
    // this the select-result bridge (e.g. alra_010's select(C,i0) value) is absent
    // from the deferral scope, gets cache-poisoned at Standard, and never reaches
    // LRA at Full. Bounded walk (cap) to keep large-corpus cost in check.
    if (egraph_) {
        const size_t kCap = 64;
        for (EufTermId s : selectTerms_) {
            addTermShared(s);                       // direct (pure-QF_AX case)
            EClassId rep = egraph_->rep(s);
            size_t walked = 0;
            for (EufTermId m : egraph_->classMembers(rep)) {
                if (++walked > kCap) break;
                addTermShared(m);                   // the bridge merged with the read
            }
        }
    } else {
        for (EufTermId s : selectTerms_) addTermShared(s);
    }
}

void ArrayReasoner::completeStoreSelects(std::deque<PendingMerge>& outQueue) {
    aniaprof::Scope _prof(aniaprof::ARR_COMPLETE);
    if (!selectCompletionEnabled_) return;
    // Total-completion budget reached (XOLVER_AX_COMPLETE_BUDGET): stop interning
    // further read-over-write selects. Sound — the model floor guards any
    // missed instance; this only bounds the driver-family blowup.
    if (completeBudget_ != 0 && completeInternsDone_ >= completeBudget_) return;
    // L1: relevancy-driven path (XOLVER_AX_LAZY) replaces the eager cross-product.
    if (lazyComplete_) { completeStoreSelectsLazy(outQueue); return; }
    discoverArrayTerms();

    // (1) Incrementally extend the read-index cache from NEW selectTerms_
    // entries since the last call. ORIGINAL formula reads only (Ext witnesses
    // are admitted separately under extWitnessComplete_). Each idx is added at
    // most once; the cache is monotonic.
    size_t nSel = selectTerms_.size();
    size_t newReadIdxStart = completeReadIdxCache_.size();
    for (size_t k = completeLastSelectScanEnd_; k < nSel; ++k) {
        EufTermId sel = selectTerms_[k];
        if (internalSelect_.count(sel)) continue;
        const auto& sn = tm_->node(sel);
        if (sn.args.size() != 2) continue;
        EufTermId idx = sn.args[1];
        ExprId idxExpr = originExpr(idx);
        if (idxExpr != NullExpr && extWitnessIdx_.count(idxExpr)) continue;
        if (completeReadIdxSeen_.insert(idx).second)
            completeReadIdxCache_.push_back(idx);
    }
    completeLastSelectScanEnd_ = nSel;
    // extWitnessComplete_ (default-OFF): admit Ext witness indices. Bounded:
    // one witness per array-disequality pair; deduped via completeReadIdxSeen_.
    if (extWitnessComplete_) {
        for (EufTermId widx : extWitnessIdxTerms_) {
            if (completeReadIdxSeen_.insert(widx).second)
                completeReadIdxCache_.push_back(widx);
        }
    }
    if (completeReadIdxCache_.empty()) return;

    // (2) Incrementally extend the array-term cache from NEW interned terms
    // since the last call. EVERY array-sorted term (store towers + bases,
    // const-arrays, array variables) participates in Row1/Row2 read-closure.
    size_t newArrayStart = completeArrayCache_.size();
    EufTermId total = static_cast<EufTermId>(tm_->termCount());
    for (EufTermId t = completeLastTermScanEnd_; t < total; ++t) {
        if (ir_->arraySortParams(tm_->node(t).sort))
            completeArrayCache_.push_back(t);
    }
    completeLastTermScanEnd_ = total;

    // (3) Cross-product, but only over the pair-frontier added since the last
    // call: (NEW arrays x ALL indices) ∪ (OLD arrays x NEW indices). The
    // remaining (OLD arrays x OLD indices) was processed in a prior call —
    // every such pair is already in selectCompleteDone_, so the original
    // full-sweep code's hash-dedup would skip them anyway. Skipping them at
    // the iteration level removes the per-call O(arrays x indices) sweep cost
    // that dominates QF_ANIA's budget once IFACE_LIFECYCLE removes the early
    // abort. Soundness: identical to the original — same pairs reach
    // internSelect, same skips, same merges enqueued.
    bool budgetHit = false;
    auto processPairs = [&](EufTermId arr, size_t idxLo, size_t idxHi) {
        ExprId arrExpr = originExpr(arr);
        if (arrExpr == NullExpr) return;
        for (size_t i = idxLo; i < idxHi; ++i) {
            // Total-completion budget: stop interning once reached (leave the
            // remaining pairs un-done; the model floor guards soundness).
            if (completeBudget_ != 0 && completeInternsDone_ >= completeBudget_) {
                budgetHit = true;
                return;
            }
            EufTermId idx = completeReadIdxCache_[i];
            uint64_t key = pairKey(arr, idx);
            if (!selectCompleteDone_.insert(key).second) continue;
            ExprId idxExpr = originExpr(idx);
            if (idxExpr == NullExpr) continue;
            internSelect(arrExpr, idxExpr, outQueue);  // counts via internSelect
        }
    };
    // NEW arrays x ALL indices (covers new x new + new x old)
    for (size_t a = newArrayStart; a < completeArrayCache_.size() && !budgetHit; ++a)
        processPairs(completeArrayCache_[a], 0, completeReadIdxCache_.size());
    // OLD arrays x NEW indices (the remaining frontier)
    if (!budgetHit && newReadIdxStart < completeReadIdxCache_.size()) {
        for (size_t a = 0; a < newArrayStart && !budgetHit; ++a)
            processPairs(completeArrayCache_[a], newReadIdxStart, completeReadIdxCache_.size());
    }
}

void ArrayReasoner::completeStoreSelectsLazy(std::deque<PendingMerge>& outQueue) {
    // RELEVANCY-DRIVEN completion (L1). For each ORIGINAL read select(B, idx),
    // intern select(s, idx) for every store s in B's e-graph class (≠ B). These
    // are exactly the store towers the read must peel THROUGH: s ~ B (same class)
    // means select(s,idx) congruence-merges with select(B,idx), and Row1/Row2 then
    // resolve s. Independent arrays (not e-graph-equal to any read array) are NOT
    // completed — that is where the eager arrays×indices cross-product exploded
    // (24k selects on cs_*). Re-run each check: classes merge during search, so
    // newly-connected stores are picked up; selectCompleteDone_ dedups; the
    // completion is monotonic and verdict-sound (only tautological selects added).
    discoverArrayTerms();
    if (storeTerms_.empty() || selectTerms_.empty()) return;

    // Group stores by e-graph class rep.
    std::unordered_map<EClassId, std::vector<EufTermId>> storesByRep;
    storesByRep.reserve(storeTerms_.size() * 2 + 1);
    for (EufTermId s : storeTerms_) storesByRep[egraph_->rep(s)].push_back(s);

    size_t nSel = selectTerms_.size();
    for (size_t k = 0; k < nSel; ++k) {
        EufTermId sel = selectTerms_[k];
        if (internalSelect_.count(sel)) continue;        // seed from genuine reads only
        const auto& sn = tm_->node(sel);
        if (sn.args.size() != 2) continue;
        EufTermId arrB = sn.args[0];
        EufTermId idx = sn.args[1];
        ExprId idxExpr = originExpr(idx);
        if (idxExpr == NullExpr) continue;
        if (extWitnessIdx_.count(idxExpr)) continue;     // parity with the eager path
        auto it = storesByRep.find(egraph_->rep(arrB));
        if (it == storesByRep.end()) continue;           // no store tower in this read's class
        for (EufTermId s : it->second) {
            if (s == arrB) continue;                     // read already on this store
            if (completeBudget_ != 0 && completeInternsDone_ >= completeBudget_) return;
            uint64_t key = pairKey(s, idx);
            if (!selectCompleteDone_.insert(key).second) continue;
            ExprId sExpr = originExpr(s);
            if (sExpr == NullExpr) continue;
            internSelect(sExpr, idxExpr, outQueue);
        }
    }
}

void ArrayReasoner::enqueueRow2CondMerges(
    const std::function<std::optional<Row2CondDiseq>(EufTermId, EufTermId)>& queryDiseq,
    int mergeLevel,
    std::deque<PendingMerge>& outQueue) {
    if (!active()) return;
    discoverArrayTerms();
    size_t r2cMerges = 0, r2cEligible = 0;
    size_t nSel = selectTerms_.size();
    for (size_t k = 0; k < nSel; ++k) {
        EufTermId selTerm = selectTerms_[k];
        const auto& seln = tm_->node(selTerm);
        if (seln.args.size() != 2) continue;
        EufTermId arrArg = seln.args[0];
        EufTermId jTerm = seln.args[1];
        EClassId arrClass = egraph_->rep(arrArg);
        for (EufTermId member : egraph_->classMembers(arrClass)) {
            if (!symIsStore(member)) continue;
            const auto& stn = tm_->node(member);
            if (stn.args.size() != 3) continue;
            EufTermId aTerm = stn.args[0];   // underlying array
            EufTermId iTerm = stn.args[1];   // write index
            if (egraph_->same(iTerm, jTerm)) continue;   // Row1 case (i=j)
            ++r2cEligible;
            auto d = queryDiseq(iTerm, jTerm);
            if (!d) continue;                            // i≠j not known → no eager merge
            ExprId jExpr = originExpr(jTerm);
            ExprId aExpr = originExpr(aTerm);
            ExprId storeExpr = originExpr(member);
            if (jExpr == NullExpr || aExpr == NullExpr || storeExpr == NullExpr) continue;
            // Build the read terms over the ACTUAL store member (soundness note in
            // instantiateLemma): select(store(a,i,v),j) and select(a,j).
            EufTermId selStore = internSelect(storeExpr, jExpr, outQueue);
            EufTermId selAJ = internSelect(aExpr, jExpr, outQueue);
            if (selStore == NullEufTerm || selAJ == NullEufTerm) continue;
            if (egraph_->same(selStore, selAJ)) continue;   // implicit dedup (backtrack-correct)
            MergeReason mr;
            mr.kind = MergeReasonKind::ArrayRow2Cond;
            mr.lit = d->reason;                              // the diseq reason literal
            mr.argPairs.push_back({iTerm, d->dForI});        // i ~ diseqLhs
            mr.argPairs.push_back({jTerm, d->dForJ});        // j ~ diseqRhs
            outQueue.push_back({selStore, selAJ, mr, mergeLevel});
            ++r2cMerges;
        }
    }
    if (xolver::env::diag("XOLVER_AX_R2D_DIAG")) {
        std::fprintf(stderr, "[R2D-merge] selects=%zu eligible=%zu merges=%zu\n",
                     nSel, r2cEligible, r2cMerges);
        std::fflush(stderr);
    }
}

void ArrayReasoner::enqueueEagerMerges(std::deque<PendingMerge>& outQueue) {
    aniaprof::Scope _prof(aniaprof::ARR_EAGER);
    if (!active()) return;
    discoverArrayTerms();
    size_t row1Merges = 0, row2Merges = 0, row2Eligible = 0;
    // Push read indices through store towers BEFORE the Row1/Const pass so the
    // selects they create get their Row1 eager-merge in this same saturation.
    completeStoreSelects(outQueue);

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
            ++row1Merges;
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

    // --- Row2 for distinct constant indices (XOLVER_AX_ROW2_CONST) ----------
    // For select(arr,j) where arr's class holds a store(a,i,v) and i,j are
    // syntactically distinct numeric/bool constants: i != j holds
    // unconditionally, so the Row2 conclusion
    //   select(store(a,i,v),j) = select(a,j)
    // is a zero-literal theorem. Merge it eagerly — no SAT split. Congruence
    // then links select(arr,j) to select(a,j) automatically. This avoids the
    // Row2 case-split lemma for the common constant-index case.
    if (row2ConstEnabled_) {
        size_t nSel = selectTerms_.size();
        for (size_t k = 0; k < nSel; ++k) {
            EufTermId selTerm = selectTerms_[k];
            const auto& seln = tm_->node(selTerm);
            if (seln.args.size() != 2) continue;
            EufTermId arrArg = seln.args[0];
            EufTermId jTerm = seln.args[1];
            EClassId arrClass = egraph_->rep(arrArg);
            for (EufTermId member : egraph_->classMembers(arrClass)) {
                if (!symIsStore(member)) continue;
                const auto& stn = tm_->node(member);
                if (stn.args.size() != 3) continue;
                EufTermId aTerm = stn.args[0];   // underlying array
                EufTermId iTerm = stn.args[1];   // write index
                if (egraph_->same(iTerm, jTerm)) continue;
                ++row2Eligible;
                if (!provablyDistinctConstIndices(iTerm, jTerm)) continue;

                ExprId jExpr = originExpr(jTerm);
                ExprId aExpr = originExpr(aTerm);
                ExprId storeExpr = originExpr(member);
                if (jExpr == NullExpr || aExpr == NullExpr || storeExpr == NullExpr) continue;

                // Build the read terms over the ACTUAL store member (see the
                // soundness note in instantiateLemma): select(store(a,i,v),j)
                // and select(a,j). Merging them is a genuine Row2 tautology.
                EufTermId selStore = internSelect(storeExpr, jExpr, outQueue);
                EufTermId selAJ = internSelect(aExpr, jExpr, outQueue);
                if (selStore == NullEufTerm || selAJ == NullEufTerm) continue;
                if (!egraph_->same(selStore, selAJ)) {
                    MergeReason mr;
                    mr.kind = MergeReasonKind::ArrayRow2;
                    mr.lit = SatLit();
                    outQueue.push_back({selStore, selAJ, mr});
                    ++row2Merges;
                }
            }
        }
    }

    static const bool axDiag = xolver::env::diag("XOLVER_AX_DIAG");
    if (axDiag) {
        std::fprintf(stderr,
            "[AX-eager] stores=%zu selects=%zu completed=%zu row1+=%zu row2Eligible=%zu row2const+=%zu\n",
            storeTerms_.size(), selectTerms_.size(),
            static_cast<size_t>(completeInternsDone_),
            row1Merges, row2Eligible, row2Merges);
        std::fflush(stderr);
    }
}

std::optional<std::vector<SatLit>>
ArrayReasoner::instantiateLemma(const std::vector<ArrayDiseq>& disequalities,
                               std::unordered_set<uint64_t>* dedupOverride) {
    aniaprof::Scope _prof(aniaprof::ARR_LEMMA);
    if (!active() || !registry_) return std::nullopt;
    discoverArrayTerms();
    std::unordered_set<uint64_t>& row2Dedup = dedupOverride ? *dedupOverride : row2Done_;

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

            // SOUNDNESS: if the write index i and the read index j are ALREADY
            // equal in the egraph (in particular when they are the same term),
            // do NOT emit a Row2 lemma. When i = j, Row1 already gives the read
            // value (select(store(a,i,v),j) = v), and the Row2 axiom
            //   i != j  =>  select(store(a,i,v),j) = select(a,j)
            // does NOT apply. Emitting the clause (i=j) OR readEq is harmful
            // here: the (i=j) disjunct is a tautology, so the clause never
            // constrains the readEq atom, leaving select(store(a,i,v),j) =
            // select(a,j) as a FREE Boolean. The SAT solver may then assert it
            // true even though it is semantically false (the correct value is
            // v, not select(a,j)), poisoning the egraph and yielding a spurious
            // conflict (a false UNSAT). Skipping the degenerate instance is
            // sound and complete: the i=j read is fully covered by Row1.
            if (egraph_->same(iTerm, jTerm)) continue;

            // Dedup by stable term ids (store member id, read index j id).
            uint64_t key = pairKey(member, jTerm);
            if (!row2Dedup.insert(key).second) continue;

            ExprId iExpr = originExpr(iTerm);
            ExprId jExpr = originExpr(jTerm);
            ExprId aExpr = originExpr(aTerm);
            ExprId storeExpr = originExpr(member);   // store(a,i,v)
            if (iExpr == NullExpr || jExpr == NullExpr ||
                aExpr == NullExpr || storeExpr == NullExpr) {
                continue;
            }

            // SOUNDNESS: the Row2 read equality MUST be built over the actual
            // store member found in arrArg's class, NOT over `selTerm` (whose
            // array argument may be a DIFFERENT store term that is only equal
            // to `member` by congruence under the current SAT assumptions).
            // Using selTerm's expr directly would assert
            //   select(arrArg, j) = select(a, j)
            // as an unconditional tautology, which is false whenever
            // arrArg != store(a,i,v) syntactically (e.g. a self-store class
            // a = store(a,i0,e0) that also contains an unrelated nested store).
            // Building select(store(a,i,v), j) keeps the lemma a genuine Row2
            // tautology; the egraph then connects it to select(arrArg, j) via
            // congruence with the proper reason chain.
            std::deque<PendingMerge> dummy;  // ensureTermRegistered side queue
            EufTermId selStore = internSelect(storeExpr, jExpr, dummy);
            EufTermId selAJ = internSelect(aExpr, jExpr, dummy);
            // (the discovered congruence merges in `dummy` are harmless to
            //  drop: they will be re-derived in the next saturation pass once
            //  these terms are registered; ensureTermRegistered already wired
            //  them into the signature table.)
            if (selStore == NullEufTerm || selAJ == NullEufTerm) continue;
            // If the Row2 conclusion already holds in the egraph (e.g. the
            // eager distinct-constant Row2 merge above derived it), the lemma is
            // redundant — skip the SAT split. Sound regardless; gated to keep
            // the flag-OFF path byte-identical.
            if (row2ConstEnabled_ && egraph_->same(selStore, selAJ)) continue;
            ExprId selStoreExpr = originExpr(selStore);  // select(store(a,i,v),j)
            ExprId selAJExpr = originExpr(selAJ);
            if (selStoreExpr == NullExpr || selAJExpr == NullExpr) continue;

            // Lemma:  (i=j)  OR  (select(store(a,i,v),j) = select(a,j))
            // The (i=j) antecedent is a shared-equality atom when the indices
            // are arith (combination); the read equality stays EUF-internal
            // (its operands are select terms, owned only by EUF/arrays).
            SatLit ijEq = makeRow2IndexEqLit(iExpr, jExpr);
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
        extWitnessIdx_.insert(kExpr);  // exclude from read-closure completion

        std::deque<PendingMerge> dummy;
        EufTermId selAK = internSelect(aExpr, kExpr, dummy);
        EufTermId selBK = internSelect(bExpr, kExpr, dummy);
        if (selAK == NullEufTerm || selBK == NullEufTerm) continue;
        // Remember the interned witness INDEX term (arg[1] of select(a,k)) so
        // completeStoreSelects can fan it through the store towers when
        // extWitnessComplete_ is on (the storeinv class). The select args[1]
        // is the EufTermId of k regardless of how internSelect deduped it.
        {
            const auto& sAKnode = tm_->node(selAK);
            if (sAKnode.args.size() == 2) extWitnessIdxTerms_.push_back(sAKnode.args[1]);
        }
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

} // namespace xolver
