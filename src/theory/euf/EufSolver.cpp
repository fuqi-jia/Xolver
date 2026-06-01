#include <cstdlib>
#include <chrono>
#include "theory/euf/EufSolver.h"
#include "theory/array/AniaProfile.h"
#include "theory/combination/CareGraph.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/datatype/DtModelValidator.h"
#include "expr/ir.h"
#include <cassert>
#include <algorithm>
#include <functional>
#include <climits>
#include <map>
#include <optional>
#include <tuple>

namespace xolver {

EufSolver::EufSolver() : egraph_(termManager_) {
    diseqWatchEnabled_ = std::getenv("XOLVER_UF_DISEQ_WATCH") != nullptr;
    eufPropEnabled_ = std::getenv("XOLVER_EUF_PROP") != nullptr;
    // Default-ON (2026-06-02 DEEP-3): Track-3 UF function-interp collection.
    // Required by the QF_UFLIA combination soundness floor (COMB_VALIDATE_SAT)
    // and harmless when not consumed downstream (just populates getModel()
    // funcInterps). A/B escape: XOLVER_EUF_UF_MODEL=0 disables.
    ufModelEnabled_ = true;
    if (const char* e = std::getenv("XOLVER_EUF_UF_MODEL")) {
        ufModelEnabled_ = !(e[0] == '0' && e[1] == '\0');
    }
    // XOLVER_EUF_MINLEVEL_HEAP (default-OFF, array-deep B2): drain saturation mergeQueue_
    // with level-bucketed map; O(n^2) → O(n log L). Same order; targets QF_ANIA/QF_AX-swap blowup.
    minLevelHeapEnabled_ = std::getenv("XOLVER_EUF_MINLEVEL_HEAP") != nullptr;
    // XOLVER_EUF_INCREMENTAL_PROP (Phase A, euf-deep): incremental entailment-prop scan.
    eufIncrementalProp_ = std::getenv("XOLVER_EUF_INCREMENTAL_PROP") != nullptr;
    eufIncrementalVerify_ = std::getenv("XOLVER_EUF_INCREMENTAL_PROP_VERIFY") != nullptr;
    if (eufIncrementalVerify_) eufIncrementalProp_ = true;  // verify implies on
    // XOLVER_EUF_PROP_DEDUP (Phase A v2): skip atoms with lemma already emitted at level<=current.
    eufPropDedup_ = std::getenv("XOLVER_EUF_PROP_DEDUP") != nullptr;
    // XOLVER_AX_STORE_MODEL (default-OFF, array-deep A1): store-aware array model
    // construction. The baseline buildArrayModel collects each array's interp
    // from DIRECT select terms only, so an array defined by a store chain
    // (a2=store(a1,i,v), a3=store(a2,j,w), …) does NOT inherit the base's
    // entries — its interp is missing the inherited writes, so the model fails
    // the store-definition assertion and an otherwise-genuine sat floors to
    // unknown (the storecomm class). This pass derives each class interp by
    // following its store/const structure (inherit base entries + apply the
    // override), then overlays explicit reads. Verdict-SOUND: model
    // construction only; the arrayModelDefinitelyViolates floor still validates,
    // so a better model recovers genuine sats and a wrong one still floors.
    storeModelEnabled_ = std::getenv("XOLVER_AX_STORE_MODEL") != nullptr;
    // E2/E3 profile triage (default-OFF): lightweight counters + chrono.
    hotProfileEnabled_ = std::getenv("XOLVER_EUF_HOTPROFILE") != nullptr;
    initializeBoolConstants();
}

EufSolver::~EufSolver() {
    if (hotProfileEnabled_ && hotProfile_.checkCalls > 0) {
        // E2/E3 hot-path triage dump (XOLVER_EUF_HOTPROFILE). Goal: identify
        // whether EUF (>50% time inside check) is the QG-classification /
        // eq_diamond perf-wall bottleneck, or whether SAT/CDCL outside check()
        // dominates (which would route the lane closure to SAT backend).
        std::cerr << "[EUF-HOTPROFILE]"
                  << " checks=" << hotProfile_.checkCalls
                  << " checkUs=" << hotProfile_.checkUs
                  << " saturationUs=" << hotProfile_.saturationUs
                  << " explainUs=" << hotProfile_.explainUs
                  << " entailUs=" << hotProfile_.entailmentUs
                  << " registerSigUs=" << hotProfile_.registerSigUs
                  << " merges=" << hotProfile_.mergesProcessed
                  << " explains=" << hotProfile_.explainCalls
                  << " entailScanRecs=" << hotProfile_.entailmentScanRecs
                  << " entailEmitted=" << hotProfile_.entailmentEmitted
                  << "\n";
    }
}

std::vector<TheoryLemma> EufSolver::takeEntailmentPropagations() {
    std::vector<TheoryLemma> out;
    auto _entT0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                     : std::chrono::steady_clock::time_point{};
    struct _EntGuard {
        bool en; std::chrono::steady_clock::time_point t0; EufHotProfile* p; std::vector<TheoryLemma>* o;
        ~_EntGuard() {
            if (en) {
                p->entailmentUs += std::chrono::duration_cast<std::chrono::microseconds>(
                    std::chrono::steady_clock::now() - t0).count();
                p->entailmentEmitted += o->size();
            }
        }
    } _g{hotProfileEnabled_, _entT0, &hotProfile_, &out};
    if (!eufPropEnabled_ || !eqAtomRegistry_ || !coreIr_) return out;
    // Propagate only from a clean, congruence-closed, conflict-free state: after
    // a Consistent check the merge queue is drained and the explanation paths
    // reflect the current assignment.
    if (pendingConflict_ || pendingUnknown_ || !mergeQueue_.empty()) return out;

    // Assigned EUF atom vars — only UNDECIDED atoms are propagation targets.
    std::unordered_set<SatVar> assigned;
    assigned.reserve(trail_.size() * 2 + 1);
    for (const auto& e : trail_) assigned.insert(e.lit.var);

    // Canonical (rep,rep) -> active-disequality index, for entailed-FALSE props.
    // Single-theory only: the combination shared bus is gated off upstream
    // (TheoryManager::takeEntailmentPropagations returns {} in combination).
    auto repPairKey = [](EClassId r1, EClassId r2) -> uint64_t {
        uint64_t lo = r1 < r2 ? r1 : r2, hi = r1 < r2 ? r2 : r1;
        return (lo << 32) | hi;
    };
    std::unordered_map<uint64_t, size_t> diseqByRepPair;
    diseqByRepPair.reserve(disequalities_.size() * 2 + 1);
    for (size_t i = 0; i < disequalities_.size(); ++i) {
        const auto& d = disequalities_[i];
        if (d.lhs == NullEufTerm || d.rhs == NullEufTerm) continue;
        EClassId ra = egraph_.rep(d.lhs), rb = egraph_.rep(d.rhs);
        if (ra == rb) continue;  // violated diseq -> conflict path handles it
        diseqByRepPair.emplace(repPairKey(ra, rb), i);
    }

    const auto& recs = eqAtomRegistry_->records();
    const size_t kMaxProps = 256;
    // Cap inner ITERATIONS too — not just emissions. On QG-classification-class
    // (qg5/qg6/qg7 quasigroup problems) the recs vector holds many thousands of
    // EUF Eq atoms; even with the 256-cap on outputs, the full O(N) sweep per
    // cb_propagate is what drives the 15-60% slowdown + loss of solves (e.g.
    // dead_dnd005 sat→timeout under EUF_PROP). Default 512; override via
    // XOLVER_EUF_PROP_BUDGET (0 = uncapped). Sound: a smaller cap only
    // emits a SUBSET of entailed lits — never an unsound one.
    static const size_t kMaxIter = [](){
        const char* v = std::getenv("XOLVER_EUF_PROP_BUDGET");
        if (v && *v) { try { return static_cast<size_t>(std::max(0, std::atoi(v))); } catch (...) {} }
        return static_cast<size_t>(512);
    }();

    // Inner: try to produce an Entailment lemma from one rec idx, push to `dst`.
    // Returns true if the rec was processed (eligible EUF Eq atom in any state),
    // false if filtered out (theory mismatch, assigned, missing term).
    auto processRec = [&](size_t idx, std::vector<TheoryLemma>& dst) -> bool {
        const auto& rec = recs[idx];
        if (rec.theory != TheoryId::EUF) return false;
        if (!std::holds_alternative<EufAtomPayload>(rec.payload)) return false;
        const auto& p = std::get<EufAtomPayload>(rec.payload);
        if (p.kind != EufAtomKind::Equality || p.rel != Relation::Eq) return false;
        SatVar v = rec.satVar;
        if (assigned.count(v)) return true;
        EufTermId s = termManager_.findTerm(p.lhs);
        EufTermId t = termManager_.findTerm(p.rhs);
        if (s == NullEufTerm || t == NullEufTerm) return true;
        EClassId rs = egraph_.rep(s), rt = egraph_.rep(t);
        if (rs == rt) {
            auto er = egraph_.explainEquality(s, t);
            if (!er.ok || er.reasons.empty()) return true;
            TheoryLemma lem;
            lem.kind = LemmaKind::Entailment;
            lem.lits.reserve(er.reasons.size() + 1);
            for (SatLit r : er.reasons) lem.lits.push_back(r.negated());
            lem.lits.push_back(SatLit{v, true});
            dst.push_back(std::move(lem));
        } else {
            auto it = diseqByRepPair.find(repPairKey(rs, rt));
            if (it == diseqByRepPair.end()) return true;
            const ActiveDisequality& d = disequalities_[it->second];
            EClassId ra = egraph_.rep(d.lhs), rb = egraph_.rep(d.rhs);
            EufTermId dS, dT;
            if (rs == ra && rt == rb) { dS = d.lhs; dT = d.rhs; }
            else if (rs == rb && rt == ra) { dS = d.rhs; dT = d.lhs; }
            else return true;
            auto e1 = egraph_.explainEquality(s, dS);
            auto e2 = egraph_.explainEquality(t, dT);
            if (!e1.ok || !e2.ok) return true;
            TheoryLemma lem;
            lem.kind = LemmaKind::Entailment;
            lem.lits.reserve(e1.reasons.size() + e2.reasons.size() + 2);
            for (SatLit r : e1.reasons) lem.lits.push_back(r.negated());
            for (SatLit r : e2.reasons) lem.lits.push_back(r.negated());
            lem.lits.push_back(d.reason.negated());
            lem.lits.push_back(SatLit{v, false});
            dst.push_back(std::move(lem));
        }
        return true;
    };

    // ------------- INCREMENTAL PATH (XOLVER_EUF_INCREMENTAL_PROP) ------------
    // Class-touch indexed scan: only re-evaluate EUF Eq atoms whose lhs/rhs term
    // (or another member of its class, post-merge) sits in a class that has had
    // a new merge since our last propagation call.
    //
    // Soundness invariants:
    //   1. forceFullEntailmentScan_ is set on backtrack (assigned-set changed,
    //      mergeRecord count regressed); next call does a full sweep that
    //      re-establishes the steady state.
    //   2. New atoms registered after last call are added to the dirty set via
    //      lastIndexedEntailmentRecCount_ extension.
    //   3. We index ONLY EUF Eq atoms (the only kind this routine emits).
    //   4. Same per-rec body (`processRec`) for both paths — no logic drift.
    // Verify mode (XOLVER_EUF_INCREMENTAL_PROP_VERIFY=1) runs the FULL scan and
    // the incremental scan, asserts equal output-lit sets — used to validate
    // the incremental implementation against the reference (assert at debug
    // print; never falsifies a verdict).
    if (eufIncrementalProp_ && !eufIncrementalVerify_) {
        size_t currentMerges = egraph_.mergeRecordCount();
        // Drift guard: if mergeRecord regressed (we missed a backtrack hook), force full.
        if (currentMerges < lastSeenMergeRecord_) forceFullEntailmentScan_ = true;

        // Lazily extend term-indexed atom map for new recs since last call.
        for (size_t i = lastIndexedEntailmentRecCount_; i < recs.size(); ++i) {
            const auto& rec = recs[i];
            if (rec.theory != TheoryId::EUF) continue;
            if (!std::holds_alternative<EufAtomPayload>(rec.payload)) continue;
            const auto& p = std::get<EufAtomPayload>(rec.payload);
            if (p.kind != EufAtomKind::Equality || p.rel != Relation::Eq) continue;
            EufTermId s = termManager_.findTerm(p.lhs);
            EufTermId t = termManager_.findTerm(p.rhs);
            if (s == NullEufTerm || t == NullEufTerm) continue;
            size_t need = std::max((size_t)s, (size_t)t) + 1;
            if (need > termToEntailmentAtomIdx_.size()) termToEntailmentAtomIdx_.resize(need);
            termToEntailmentAtomIdx_[s].push_back(i);
            if (s != t) termToEntailmentAtomIdx_[t].push_back(i);
        }
        lastIndexedEntailmentRecCount_ = recs.size();

        // Build dirty set.
        std::vector<size_t> toScan;
        // Cap how many members we walk per merge before giving up (large classes
        // make incremental scan more expensive than full scan).
        const size_t kMemberWalkCap = 256;
        bool fellBackToFull = false;
        if (forceFullEntailmentScan_) {
            fellBackToFull = true;
        } else {
            std::unordered_set<size_t> dirty;
            for (size_t m = lastSeenMergeRecord_; m < currentMerges; ++m) {
                const MergeRecord& mr = egraph_.mergeRecord(m);
                // Walk classMembers of the merged class — catches atoms whose
                // term is in the same class but isn't literally mr.lhs/mr.rhs.
                EClassId rep = mr.kept != NullEClass ? mr.kept : egraph_.rep(mr.lhs);
                const auto& mems = egraph_.classMembers(rep);
                if (mems.size() > kMemberWalkCap) { fellBackToFull = true; break; }
                for (EufTermId mem : mems) {
                    if ((size_t)mem < termToEntailmentAtomIdx_.size()) {
                        for (size_t idx : termToEntailmentAtomIdx_[mem]) dirty.insert(idx);
                    }
                }
            }
            if (!fellBackToFull) toScan.assign(dirty.begin(), dirty.end());
        }
        lastSeenMergeRecord_ = currentMerges;
        forceFullEntailmentScan_ = false;

        if (fellBackToFull) {
            size_t iterations = 0;
            for (size_t i = 0; i < recs.size(); ++i) {
                if (kMaxIter > 0 && ++iterations > kMaxIter) break;
                if (out.size() >= kMaxProps) break;
                if (!processRec(i, out)) continue;
            }
        } else {
            size_t iterations = 0;
            for (size_t idx : toScan) {
                if (kMaxIter > 0 && ++iterations > kMaxIter) break;
                if (out.size() >= kMaxProps) break;
                processRec(idx, out);
            }
        }
        return out;
    }

    // ------------- VERIFY PATH: full + incremental compare ------------
    if (eufIncrementalVerify_) {
        std::vector<TheoryLemma> fullOut;
        size_t iterations = 0;
        for (size_t i = 0; i < recs.size(); ++i) {
            if (kMaxIter > 0 && ++iterations > kMaxIter) break;
            if (fullOut.size() >= kMaxProps) break;
            processRec(i, fullOut);
        }
        // Now run incremental shadow.
        std::vector<TheoryLemma> incOut;
        {
            size_t currentMerges = egraph_.mergeRecordCount();
            if (currentMerges < lastSeenMergeRecord_) forceFullEntailmentScan_ = true;
            for (size_t i = lastIndexedEntailmentRecCount_; i < recs.size(); ++i) {
                const auto& rec = recs[i];
                if (rec.theory != TheoryId::EUF) continue;
                if (!std::holds_alternative<EufAtomPayload>(rec.payload)) continue;
                const auto& p = std::get<EufAtomPayload>(rec.payload);
                if (p.kind != EufAtomKind::Equality || p.rel != Relation::Eq) continue;
                EufTermId s = termManager_.findTerm(p.lhs);
                EufTermId t = termManager_.findTerm(p.rhs);
                if (s == NullEufTerm || t == NullEufTerm) continue;
                size_t need = std::max((size_t)s, (size_t)t) + 1;
                if (need > termToEntailmentAtomIdx_.size()) termToEntailmentAtomIdx_.resize(need);
                termToEntailmentAtomIdx_[s].push_back(i);
                if (s != t) termToEntailmentAtomIdx_[t].push_back(i);
            }
            lastIndexedEntailmentRecCount_ = recs.size();
            std::vector<size_t> toScan;
            bool full = forceFullEntailmentScan_;
            if (!full) {
                std::unordered_set<size_t> dirty;
                for (size_t m = lastSeenMergeRecord_; m < currentMerges; ++m) {
                    const MergeRecord& mr = egraph_.mergeRecord(m);
                    EClassId rep = mr.kept != NullEClass ? mr.kept : egraph_.rep(mr.lhs);
                    for (EufTermId mem : egraph_.classMembers(rep)) {
                        if ((size_t)mem < termToEntailmentAtomIdx_.size()) {
                            for (size_t idx : termToEntailmentAtomIdx_[mem]) dirty.insert(idx);
                        }
                    }
                }
                toScan.assign(dirty.begin(), dirty.end());
            }
            lastSeenMergeRecord_ = currentMerges;
            forceFullEntailmentScan_ = false;
            if (full) {
                size_t it = 0;
                for (size_t i = 0; i < recs.size(); ++i) {
                    if (kMaxIter > 0 && ++it > kMaxIter) break;
                    if (incOut.size() >= kMaxProps) break;
                    processRec(i, incOut);
                }
            } else {
                size_t it = 0;
                for (size_t idx : toScan) {
                    if (kMaxIter > 0 && ++it > kMaxIter) break;
                    if (incOut.size() >= kMaxProps) break;
                    processRec(idx, incOut);
                }
            }
        }
        // Compare: incremental must be a SUBSET of full (the soundness check).
        // The full sweep re-emits previously-fired lemmas on every call (the SAT
        // layer is responsible for deduping them via assigned/lemmaDb); the
        // incremental sweep only emits atoms whose entailment status JUST became
        // visible since the last call. So inc ⊆ full is the correct invariant.
        // Anything emitted by inc that is NOT emitted by full is a real bug
        // (would mean inc invents an entailment).
        auto lemmaKey = [](const TheoryLemma& l) -> std::string {
            std::string s; s.reserve(l.lits.size() * 8);
            for (SatLit lt : l.lits) {
                s += std::to_string(lt.var);
                s += (lt.sign ? '+' : '-');
                s += '|';
            }
            return s;
        };
        std::unordered_set<std::string> fullKeys;
        for (const auto& l : fullOut) fullKeys.insert(lemmaKey(l));
        size_t spurious = 0;
        for (const auto& l : incOut) {
            if (!fullKeys.count(lemmaKey(l))) ++spurious;
        }
        if (spurious > 0) {
            std::cerr << "[EUF-INC-VERIFY] SPURIOUS inc emissions: " << spurious
                      << " (full=" << fullOut.size() << " inc=" << incOut.size() << ")\n";
            for (const auto& l : incOut) {
                auto k = lemmaKey(l);
                if (!fullKeys.count(k)) std::cerr << "  spurious: " << k << "\n";
            }
        }
        return fullOut;  // verify mode emits the reference output (sound)
    }

    // ------------- DEFAULT PATH: original full sweep ------------
    // With XOLVER_EUF_PROP_DEDUP: skip atoms whose lemma we already emitted at a
    // level still in scope (SAT's lemmaDb still holds it; re-emitting is wasted
    // work). emittedAtomLevel_ is invalidated on backtrack via
    // dropEmittedAboveLevel.
    if (eufPropDedup_ && emittedAtomLevel_.size() < recs.size()) {
        emittedAtomLevel_.resize(recs.size(), -1);
    }
    size_t iterations = 0;
    for (size_t i = 0; i < recs.size(); ++i) {
        if (kMaxIter > 0 && ++iterations > kMaxIter) break;
        if (out.size() >= kMaxProps) break;
        if (eufPropDedup_ && (size_t)i < emittedAtomLevel_.size()
            && emittedAtomLevel_[i] >= 0 && emittedAtomLevel_[i] <= currentLevel_) {
            continue;  // already emitted at a still-in-scope level
        }
        size_t before = out.size();
        processRec(i, out);
        if (eufPropDedup_ && out.size() > before) {
            if ((size_t)i >= emittedAtomLevel_.size())
                emittedAtomLevel_.resize((size_t)i + 1, -1);
            emittedAtomLevel_[i] = currentLevel_;
        }
    }
    return out;
}

void EufSolver::rebuildDiseqIndex() {
    diseqByTerm_.clear();
    for (uint32_t i = 0; i < disequalities_.size(); ++i) {
        diseqByTerm_[disequalities_[i].lhs].push_back({i, 0});
        diseqByTerm_[disequalities_[i].rhs].push_back({i, 0});
    }
    for (uint32_t i = 0; i < sharedDisequalities_.size(); ++i) {
        diseqByTerm_[sharedDisequalities_[i].lhs].push_back({i, 1});
        diseqByTerm_[sharedDisequalities_[i].rhs].push_back({i, 1});
    }
}

TheoryConflict EufSolver::buildDiseqConflict(const ActiveDisequality& d) {
    auto er = egraph_.explainEquality(d.lhs, d.rhs);
    std::vector<SatLit> reasons = er.ok ? std::move(er.reasons) : allActiveReasons();
    reasons.push_back(d.reason);
    return TheoryConflict{std::move(reasons)};
}

int EufSolver::debugCountStaleMerges() const {
    std::unordered_set<uint64_t> asserted;
    for (const auto& e : trail_)
        asserted.insert((uint64_t(e.lit.var) << 1) | (e.lit.sign ? 1u : 0u));
    int stale = 0;
    for (size_t i = 0; i < egraph_.mergeRecordCount(); ++i) {
        const auto& rec = egraph_.mergeRecord(i);
        if (!rec.merged || rec.reason.kind != MergeReasonKind::AssertedEquality) continue;
        SatLit l = rec.reason.lit;
        if (!asserted.count((uint64_t(l.var) << 1) | (l.sign ? 1u : 0u))) ++stale;
    }
    return stale;
}

bool EufSolver::satComplete(std::string* reason) const {
    auto fail = [&](const char* r) { if (reason) *reason = r; return false; };
    // EUF base: congruence closure is a COMPLETE decision procedure, so a
    // congruence-closed egraph with all asserted (dis)equalities satisfied and
    // nothing pending IS a positive completeness proof — even over opaque sorts.
    // After a Consistent check the saturation loop has drained: an empty merge
    // queue with no pending verdict means congruence is closed by construction
    // (the explicit congruenceClosed() check is debug-only / NDEBUG-gated).
    if (pendingConflict_) return fail("euf: pending conflict");
    if (pendingUnknown_)  return fail("euf: pending unknown");
    if (!mergeQueue_.empty()) return fail("euf: pending merges");
    for (const auto& d : disequalities_)
        if (egraph_.same(d.lhs, d.rhs)) return fail("euf: asserted disequality violated");
    for (const auto& d : sharedDisequalities_)
        if (egraph_.same(d.lhs, d.rhs)) return fail("euf: shared disequality violated");

    // Datatype completeness gate. The DtReasoner detects every DT conflict
    // (clash / injectivity / projection / tester / acyclicity), so a Consistent
    // check means none is present; a `sat` is then SOUND iff the DT structure is
    // a concrete ground-term model — i.e. every datatype e-class has a
    // determined constructor. If some datatype class is constructor-undetermined
    // the procedure is incomplete here (no exhaustiveness split yet) so we block
    // the sat to unknown rather than risk a false sat. Replaces the old blanket
    // DT-sat floor with a precise, recovering gate.
    if (dtMode_ && !dtReasoner_.modelFullyDetermined()) {
        return fail("dt: model not fully determined (a datatype class has no constructor)");
    }

    // Array obligation detector (Phase 0). EUF congruence closure does NOT
    // discharge the array axioms; an undischarged obligation leaves a model EUF
    // locally accepts but that violates extensionality (array_incompleteness1).
    if (arrayMode_) {
        std::vector<EufTermId> stores;
        for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
            const auto& n = termManager_.node(t);
            if (n.args.empty()) continue;
            if (termManager_.symbolName(n.symbol) == "#array.store") stores.push_back(t);
        }
        // Store-equality-decomposition obligation: two store terms that are
        // congruent (same egraph class) but whose (base,index,value) are not all
        // congruent encode store(a,i,v)=store(a',j,w), entailing extensional
        // consequences the reasoner has NOT applied -> cannot certify completeness.
        for (size_t p = 0; p < stores.size(); ++p) {
            for (size_t q = p + 1; q < stores.size(); ++q) {
                EufTermId s1 = stores[p], s2 = stores[q];
                if (!egraph_.same(s1, s2)) continue;
                const auto& a1 = termManager_.node(s1).args;
                const auto& a2 = termManager_.node(s2).args;
                if (a1.size() != 3 || a2.size() != 3) continue;
                if (!(egraph_.same(a1[0], a2[0]) && egraph_.same(a1[1], a2[1]) &&
                      egraph_.same(a1[2], a2[2])))
                    return fail("euf/array: undischarged store-equality decomposition");
            }
        }
        // Any array-sort disequality requires an extensionality witness (a
        // differing select); we do not yet track witnesses, so it cannot be
        // positively certified -> floor.
        auto isArraySort = [&](EufTermId t) {
            if (t == NullEufTerm || !coreIr_) return false;
            return coreIr_->arraySortParams(termManager_.node(t).sort).has_value();
        };
        for (const auto& d : disequalities_)
            if (isArraySort(d.lhs) && isArraySort(d.rhs))
                return fail("euf/array: array disequality without extensionality witness");
        for (const auto& d : sharedDisequalities_)
            if (isArraySort(d.lhs) && isArraySort(d.rhs))
                return fail("euf/array: shared array disequality without witness");
    }
    return true;
}

std::vector<std::pair<SharedTermId, SharedTermId>>
EufSolver::collectArrangeableUfArgPairs(
    const std::function<bool(SharedTermId, SharedTermId)>& valueEqual) const {
    std::vector<std::pair<SharedTermId, SharedTermId>> pairs;
    // Reverse map: EufTermId -> SharedTermId (interface constants/bridge vars).
    std::unordered_map<EufTermId, SharedTermId> eufToShared;
    eufToShared.reserve(sharedTermToEufTerm_.size());
    for (const auto& [s, t] : sharedTermToEufTerm_) eufToShared.emplace(t, s);

    // Application terms grouped by (symbol, arity), skipping arithmetic builtins
    // (#builtin.*) — interpreted by the arith solver, not EUF congruence. User
    // UF + #array.select/store are congruence-relevant.
    std::unordered_map<uint64_t, std::vector<EufTermId>> byKind;
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        const auto& n = termManager_.node(t);
        if (n.args.empty()) continue;
        if (termManager_.symbolName(n.symbol).rfind("#builtin.", 0) == 0) continue;
        uint64_t key = (static_cast<uint64_t>(n.symbol) << 8) | (n.args.size() & 0xff);
        byKind[key].push_back(t);
    }
    auto sharedOf = [&](EufTermId t) -> SharedTermId {
        auto it = eufToShared.find(t);
        return it == eufToShared.end() ? static_cast<SharedTermId>(-1) : it->second;
    };
    // Two applications are a genuine arrangement obligation only if they are
    // KNOWN-DISEQUAL (an asserted (distinct ...) puts their classes apart): then
    // arranging their args equal would force a congruence that contradicts the
    // disequality. If the apps are merely forced apart by ARITH (e.g. f(a)<f(b)
    // on the bridged results, which EUF does not see), the coincidence of the
    // args is breakable by the arith model (arrange args unequal) -> NOT an
    // obligation, and flooring it would over-floor a satisfiable formula.
    auto appsKnownDisequal = [&](EufTermId t1, EufTermId t2) -> bool {
        auto match = [&](const ActiveDisequality& d) {
            return (egraph_.same(t1, d.lhs) && egraph_.same(t2, d.rhs)) ||
                   (egraph_.same(t1, d.rhs) && egraph_.same(t2, d.lhs));
        };
        for (const auto& d : disequalities_)       if (match(d)) return true;
        for (const auto& d : sharedDisequalities_) if (match(d)) return true;
        return false;
    };
    for (auto& [key, apps] : byKind) {
        (void)key;
        for (size_t p = 0; p < apps.size(); ++p) {
            for (size_t q = p + 1; q < apps.size(); ++q) {
                EufTermId t1 = apps[p], t2 = apps[q];
                if (egraph_.same(t1, t2)) continue;
                if (!appsKnownDisequal(t1, t2)) continue;
                const auto& a1 = termManager_.node(t1).args;
                const auto& a2 = termManager_.node(t2).args;
                if (a1.size() != a2.size()) continue;
                // Every differing position must be a SHARED, value-equal pair for
                // arranging to force congruence; otherwise the pair is not
                // arrangeable and we skip it (do not split).
                std::vector<std::pair<SharedTermId, SharedTermId>> diff;
                bool arrangeable = true;
                for (size_t i = 0; i < a1.size(); ++i) {
                    if (egraph_.same(a1[i], a2[i])) continue;
                    SharedTermId s1 = sharedOf(a1[i]), s2 = sharedOf(a2[i]);
                    if (s1 == static_cast<SharedTermId>(-1) ||
                        s2 == static_cast<SharedTermId>(-1) ||
                        !valueEqual(s1, s2)) { arrangeable = false; break; }
                    diff.emplace_back(s1, s2);
                }
                if (arrangeable && !diff.empty())
                    for (auto& d : diff) pairs.push_back(d);
            }
        }
    }
    return pairs;
}

bool EufSolver::hasUnarrangedUfCongruence(
    const std::function<bool(SharedTermId, SharedTermId)>& valueEqual,
    std::string* reason) const {
    if (!collectArrangeableUfArgPairs(valueEqual).empty()) {
        if (reason) *reason = "combination: unarranged UF-argument congruence "
                              "(shared bridge-var/arg value-equal but not merged)";
        return true;
    }
    return false;
}

void EufSolver::push() {
    scopeLimits_.push_back(trail_.size());
    scopeSnapshots_.push_back(egraph_.snapshot());
}

void EufSolver::pop(uint32_t n) {
    while (n-- && !scopeLimits_.empty()) {
        size_t limit = scopeLimits_.back();
        EGraphSnapshot snap = scopeSnapshots_.back();

        trail_.resize(limit);

        // remove disequalities whose assignment was popped
        auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
            [limit](const auto& d) { return d.trailIndex >= limit; });
        disequalities_.erase(dit, disequalities_.end());

        mergeQueue_.clear();

        egraph_.rollback(snap);

        // Reset bool marks: recompute from current egraph roots
        for (auto& info : classInfo_) {
            info.boolMark = BoolConstMark::None;
        }
        if (trueTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
        }
        if (falseTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
        }

        pendingConflict_.reset();
        pendingUnknown_ = false;

        // Decision-level egraph boundaries are scoped to a single solve; a scope
        // pop returns to the assertion stack (decision level 0), so discard them.
        egraphBoundaries_.clear();

        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }
}

void EufSolver::reset() {
    modelSnapshot_.reset();
    trail_.clear();
    scopeLimits_.clear();
    scopeSnapshots_.clear();
    egraphBoundaries_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    pendingUnknown_ = false;
    termManager_.clear();
    egraph_.clear();
    sharedTermToEufTerm_.clear();
    sharedDisequalities_.clear();

    classInfo_.clear();
    mergeQueue_.clear();
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;

    arrayReasoner_.reset();
    dtReasoner_.reset();

    initializeBoolConstants();
}

void EufSolver::ensureDtContext() {
    if (!dtMode_ || !coreIr_) return;
    if (!dtReasoner_.active()) {
        dtReasoner_.setContext(&termManager_, &egraph_, coreIr_, dtRegistry_);
    }
    dtReasoner_.setBoolConstants(trueTerm_, falseTerm_);
    // Combination logics (QF_UFDTNIA/LIA) carry a shared-term registry; pure
    // QF_UFDT does not. Drives the finite-DT N-O completeness floor.
    dtReasoner_.setCombinationMode(sharedTermRegistry_ != nullptr);
}

void EufSolver::ensureArrayContext() {
    if (!arrayMode_ || !coreIr_) return;
    if (!arrayReasoner_.active()) {
        arrayReasoner_.setContext(&termManager_, &egraph_, coreIr_, arrayRegistry_);
        // In combination logics the indices/elements are shared arith terms;
        // hand the reasoner the SharedTermRegistry so Row2 builds (i=j) as a
        // shared-equality atom. Null in pure QF_AX.
        arrayReasoner_.setSharedTermRegistry(sharedTermRegistry_);
    }
}

std::vector<SharedTermId> EufSolver::arrayIndexSharedTerms() const {
    std::unordered_set<SharedTermId> set;
    if (arrayMode_) arrayReasoner_.collectIndexSharedTerms(set);
    return std::vector<SharedTermId>(set.begin(), set.end());
}

std::vector<ArrayReasoner::ArrayDiseq> EufSolver::activeArrayDiseqs() const {
    std::vector<ArrayReasoner::ArrayDiseq> out;
    if (!arrayMode_ || !coreIr_) return out;
    auto isArraySort = [&](EufTermId t) {
        if (t == NullEufTerm) return false;
        return coreIr_->arraySortParams(termManager_.node(t).sort).has_value();
    };
    // Direct array disequalities (a != b asserted locally).
    for (const auto& d : disequalities_) {
        if (isArraySort(d.lhs) && isArraySort(d.rhs)) {
            out.push_back({d.lhs, d.rhs});
        }
    }

    // Congruence-contrapositive extensionality routing (XOLVER_ARRAY_CONGR_EXT).
    // A disequality  h(..p..) != h(..q..)  between two applications of the SAME
    // function symbol that differ in EXACTLY ONE argument position soundly
    // entails  arg_p != arg_q  at that position (if they were equal the apps
    // would be congruent, hence equal, contradicting the diseq). When that arg
    // is array-sorted we surface (arg_p, arg_q) so Extensionality splits on it
    // (array_incompleteness1: g(a)!=g(b) ==> a!=b ==> select(a,k)!=select(b,k)).
    //
    // The diseq may live LOCALLY (disequalities_) or, after purification in
    // combination, on the SHARED bus as a scalar  s1 != s2  with the egraph
    // holding s1 = h(..p..), s2 = h(..q..). Matching disequalities by egraph
    // CLASS (egraph_.same), not by literal endpoints, covers both — this is the
    // "shared-bus scalar-only gap" fix.
    //
    // SOUNDNESS: the Ext lemma this feeds (a=b OR select(a,k)!=select(b,k)) is a
    // tautology, so emitting it for any pair is sound regardless of whether the
    // diseq is truly entailed; the contrapositive only governs WHICH pairs are
    // worth splitting on (precision + termination), never the verdict. The Ext
    // site re-checks array-sortedness as a second guard.
    static const bool congrExt = std::getenv("XOLVER_ARRAY_CONGR_EXT") != nullptr;
    if (congrExt) {
        // Group application terms by (symbol, arity). Restrict to USER-declared
        // functions: skip ALL internal symbols (#array.*, #builtin.*, #dt.*, …).
        // Array builtins (select/store) have dedicated Row1/Row2/Ext reasoning;
        // piggybacking the contrapositive on synthesized internal selects over a
        // self-store class explodes Ext with fresh witness indices (alra_010).
        // A user UF over arrays (g:Array->Int) is the genuine external observer
        // whose result-diseq forces an array-arg diseq (array_incompleteness1).
        std::unordered_map<uint64_t, std::vector<EufTermId>> byKind;
        for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
            const auto& n = termManager_.node(t);
            if (n.args.empty()) continue;
            if (termManager_.symbolName(n.symbol).rfind("#", 0) == 0) continue;
            uint64_t key = (static_cast<uint64_t>(n.symbol) << 8) | (n.args.size() & 0xff);
            byKind[key].push_back(t);
        }
        auto appsKnownDisequal = [&](EufTermId t1, EufTermId t2) -> bool {
            auto match = [&](const ActiveDisequality& d) {
                return (egraph_.same(t1, d.lhs) && egraph_.same(t2, d.rhs)) ||
                       (egraph_.same(t1, d.rhs) && egraph_.same(t2, d.lhs));
            };
            for (const auto& d : disequalities_)       if (match(d)) return true;
            for (const auto& d : sharedDisequalities_) if (match(d)) return true;
            return false;
        };
        std::unordered_set<uint64_t> emitted;
        for (auto& kv : byKind) {
            auto& apps = kv.second;
            for (size_t p = 0; p < apps.size(); ++p) {
                for (size_t q = p + 1; q < apps.size(); ++q) {
                    EufTermId t1 = apps[p], t2 = apps[q];
                    // Trigger only on SCALAR-result user applications (e.g.
                    // g:Array->Int). A user UF returning an ARRAY (h:X->Array) being
                    // disequal is itself array-level — handled by the direct
                    // array-diseq scan above — so skip it here to avoid redundant
                    // Ext fan-out.
                    if (isArraySort(t1)) continue;
                    if (egraph_.same(t1, t2)) continue;
                    if (!appsKnownDisequal(t1, t2)) continue;
                    const auto& a1 = termManager_.node(t1).args;
                    const auto& a2 = termManager_.node(t2).args;
                    if (a1.size() != a2.size()) continue;
                    int diffPos = -1;
                    bool single = true;
                    for (size_t i = 0; i < a1.size(); ++i) {
                        if (egraph_.same(a1[i], a2[i])) continue;
                        if (diffPos != -1) { single = false; break; }
                        diffPos = static_cast<int>(i);
                    }
                    if (!single || diffPos == -1) continue;
                    EufTermId pArg = a1[diffPos], qArg = a2[diffPos];
                    if (!isArraySort(pArg) || !isArraySort(qArg)) continue;
                    uint64_t lo = pArg < qArg ? pArg : qArg;
                    uint64_t hi = pArg < qArg ? qArg : pArg;
                    uint64_t dk = (lo << 32) | hi;
                    if (!emitted.insert(dk).second) continue;
                    out.push_back({pArg, qArg});
                }
            }
        }
    }
    return out;
}

void EufSolver::recordEgraphBoundary(int level) {
    // Record the egraph snapshot as the boundary for `level` (state before this
    // level's merges) the first time check() begins processing merges at this
    // level. Boundaries are kept sorted ascending; since check() processes
    // merges in ascending level order, levels arrive non-decreasing.
    if (!egraphBoundaries_.empty() && egraphBoundaries_.back().level >= level) return;
    egraphBoundaries_.push_back({level, egraph_.snapshot()});
}

void EufSolver::backtrackToLevel(int target) {
    currentLevel_ = target;
    // Force a full entailment sweep on the next propagation call: the assigned
    // set changed and the mergeRecord count is about to regress, so the
    // class-touch dirty index built from prior merges is no longer authoritative.
    forceFullEntailmentScan_ = true;
    lastSeenMergeRecord_ = 0;
    // XOLVER_EUF_PROP_DEDUP: invalidate emissions at levels > target. The lemmas
    // are still in SAT's lemmaDb (which has its own backtrack semantics), but
    // their entailment condition may now be unmet so we must consider re-emitting.
    if (eufPropDedup_) {
        for (auto& lvl : emittedAtomLevel_) {
            if (lvl > target) lvl = -1;
        }
    }

    // Trail: keep entries with level <= target. The SAT decision trail is
    // level-ordered (ascending), so the kept entries are a prefix.
    size_t keep = trail_.size();
    for (size_t i = 0; i < trail_.size(); ++i) {
        if (trail_[i].level > target) { keep = i; break; }
    }
    trail_.resize(keep);

    // Drop disequalities / shared disequalities / queued merges above target.
    auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    disequalities_.erase(dit, disequalities_.end());

    auto sdIt = std::remove_if(sharedDisequalities_.begin(), sharedDisequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    sharedDisequalities_.erase(sdIt, sharedDisequalities_.end());

    auto mqIt = std::remove_if(mergeQueue_.begin(), mergeQueue_.end(),
        [target](const auto& m) { return m.level > target; });
    mergeQueue_.erase(mqIt, mergeQueue_.end());

    // Egraph: restore the boundary of the SMALLEST level > target — its
    // egraphBefore is the state after all level-<=target merges (boundaries are
    // recorded in level order, and the saturation applies merges level-ordered,
    // so the size-based undo is level-monotonic). If no level > target produced
    // merges, the egraph is already at the target state.
    const EgraphBoundary* restore = nullptr;
    for (const auto& b : egraphBoundaries_) {
        if (b.level > target) { restore = &b; break; }
    }
    if (restore) egraph_.rollback(restore->egraphBefore);
    while (!egraphBoundaries_.empty() && egraphBoundaries_.back().level > target)
        egraphBoundaries_.pop_back();

    // clean scope stack if needed
    while (!scopeLimits_.empty() && scopeLimits_.back() > trail_.size()) {
        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }

    // Reset bool marks: recompute from current egraph roots
    for (auto& info : classInfo_) {
        info.boolMark = BoolConstMark::None;
    }
    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    pendingConflict_.reset();
    pendingUnknown_ = false;
}

void EufSolver::initializeBoolConstants() {
    trueTerm_ = termManager_.internTrueConstant();
    falseTerm_ = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm_);
    egraph_.setFalseTerm(falseTerm_);
    egraph_.ensureTermRegistered(trueTerm_, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm_, mergeQueue_);

    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }
}

EufSolver::EClassInfo& EufSolver::classInfo(EClassId id) {
    if (classInfo_.size() <= id) classInfo_.resize(id + 1);
    return classInfo_[id];
}

EufSolver::BoolConstMark EufSolver::mergeBoolMark(BoolConstMark a, BoolConstMark b) {
    if (a == BoolConstMark::Both || b == BoolConstMark::Both) return BoolConstMark::Both;
    if (a == BoolConstMark::None) return b;
    if (b == BoolConstMark::None) return a;
    if (a == b) return a;
    return BoolConstMark::Both;
}

std::vector<SatLit> EufSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    reasons.reserve(trail_.size() + disequalities_.size() + sharedDisequalities_.size());
    for (const auto& e : trail_) {
        reasons.push_back(e.lit);
    }
    for (const auto& d : disequalities_) {
        reasons.push_back(d.reason);
    }
    for (const auto& d : sharedDisequalities_) {
        reasons.push_back(d.reason);
    }
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), reasons.end());
    return reasons;
}

void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] BOOL-BOTH kept=" << kept << " killed=" << killed
                      << " kMark=" << (int)kInfo.boolMark << " dMark=" << (int)dInfo.boolMark
                      << " explainTF.ok=" << er.ok << " chain=" << er.reasons.size()
                      << " trueRep=" << egraph_.rep(trueTerm_) << " falseRep=" << egraph_.rep(falseTerm_) << "\n";
        }
        if (er.ok && egraph_.same(trueTerm_, falseTerm_)) {
            pendingConflict_ = TheoryConflict{std::move(er.reasons)};
        } else {
            // SOUNDNESS: a Both boolMark means this class is tagged as
            // containing a term equal to `true` AND a term equal to `false`.
            // But the mark is propagated by class-merge bookkeeping
            // (mergeBoolMark) which, in rare orderings driven by array
            // Row1/Row2 reasoning over compound/bridge indices, can tag a
            // class Both even though the genuine `true` and `false` constant
            // terms are NOT in the same egraph class (here trueRep != falseRep,
            // so explainEquality(true,false) correctly reports !ok — there is
            // no real true == false derivation). Emitting allActiveReasons() as
            // a conflict in that case is UNSOUND: it asserts that the current,
            // perfectly satisfiable assignment is contradictory, producing a
            // spurious UNSAT (observed as an intermittent false-unsat on
            // QF_A(UF)L(I/R)A formulas with purified compound array indices).
            //
            // Only emit a conflict when true and false are genuinely merged
            // (the `ok` branch above, which carries a real reason chain). When
            // they are not, there is no sound conflict to report; fall through
            // without setting pendingConflict_. Congruence continues normally
            // and the model is validated by the exact kernel before any SAT is
            // returned, so soundness is preserved. At worst this is incomplete
            // (the genuine conflict, if any, is found via another path or the
            // result is Unknown) — never a wrong verdict.
            NO_DBG << "[EUF] BOOL-BOTH mark without a real true==false merge "
                      "(trueRep != falseRep); suppressing unsound fallback conflict\n";
        }

    }
}

// ---------------------------------------------------------------------------
// assertLit
// ---------------------------------------------------------------------------

void EufSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<EufAtomPayload>(atom.payload)) return;
    const auto& payload = std::get<EufAtomPayload>(atom.payload);

    currentLevel_ = std::max(currentLevel_, level);

    // Everything this assertLit queues (term-registration congruences + the
    // asserted merge) belongs to `level`; tag from here so the level-ordered
    // saturation and the level-aware backtrack treat it consistently.
    size_t mqBefore = mergeQueue_.size();
    auto tagFromHere = [&]() {
        for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    };

    // Lazily intern true/false constants
    EufTermId trueTerm = termManager_.internTrueConstant();
    EufTermId falseTerm = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm);
    egraph_.setFalseTerm(falseTerm);
    egraph_.ensureTermRegistered(trueTerm, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm, mergeQueue_);

    // Update our cached true/false roots if they changed
    if (trueTerm_ == NullEufTerm) {
        trueTerm_ = trueTerm;
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ == NullEufTerm) {
        falseTerm_ = falseTerm;
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    // Intern lhs/rhs (monotonic)
    EufTermId lhs = termManager_.intern(payload.lhs, *coreIr_);
    EufTermId rhs = termManager_.intern(payload.rhs, *coreIr_);
    if (lhs == NullEufTerm || rhs == NullEufTerm) {
        pendingUnknown_ = true;
        tagFromHere();
        return;
    }

    egraph_.ensureTermRegistered(lhs, mergeQueue_);
    egraph_.ensureTermRegistered(rhs, mergeQueue_);

    if (payload.kind == EufAtomKind::BoolTermAsFormula) {
        EufTermId target = value ? trueTerm : falseTerm;
        trail_.push_back({level, reason, atom, value});
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, target, mr});
        tagFromHere();
        return;
    }

    bool isEq = false;
    if (payload.rel == Relation::Eq) {
        isEq = value;
    } else if (payload.rel == Relation::Neq) {
        isEq = !value;
    } else {
        tagFromHere();
        return;
    }

    size_t trailIdx = trail_.size();
    trail_.push_back({level, reason, atom, value});

    if (isEq) {
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, rhs, mr});
    } else {
        disequalities_.push_back({lhs, rhs, reason, level, trailIdx});
    }
    tagFromHere();
}

// ---------------------------------------------------------------------------
// check — 唯一 saturation loop
// ---------------------------------------------------------------------------

TheoryCheckResult EufSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    aniaprof::init();
    aniaprof::Scope _profCheck(aniaprof::EUF_CHECK);
    auto _checkT0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                       : std::chrono::steady_clock::time_point{};
    if (hotProfileEnabled_) {
        ++hotProfile_.checkCalls;
        // Periodic dump so a SIGKILL'd timeout still produces signal. Every
        // 1000 checks (low-overhead even on QG-class with 1e6 checks).
        if (hotProfile_.checkCalls % 1000 == 0) {
            std::cerr << "[EUF-HOTPROFILE@" << hotProfile_.checkCalls << "]"
                      << " checkUs=" << hotProfile_.checkUs
                      << " saturationUs=" << hotProfile_.saturationUs
                      << " entailUs=" << hotProfile_.entailmentUs
                      << " registerSigUs=" << hotProfile_.registerSigUs
                      << " merges=" << hotProfile_.mergesProcessed
                      << " entailEmitted=" << hotProfile_.entailmentEmitted
                      << std::endl;  // flush so SIGKILL'd progress is preserved
        }
    }
    struct _CheckGuard {
        bool en; std::chrono::steady_clock::time_point t0; EufHotProfile* p;
        ~_CheckGuard() {
            if (en) p->checkUs += std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - t0).count();
        }
    } _g{hotProfileEnabled_, _checkT0, &hotProfile_};
    if (pendingUnknown_) {
        return TheoryCheckResult::unknown();
    }
    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(*pendingConflict_);
    }

    if (std::getenv("EUF_VERIFY")) {
        int stale = debugCountStaleMerges();
        if (stale > 0)
            fprintf(stderr, "[STALE_MERGE@check] count=%d records=%zu trail=%zu\n",
                    stale, egraph_.mergeRecordCount(), trail_.size());
    }

    // Array Row1/Const eager merges + signature registration produce
    // tautological / congruence consequences at the current decision level.
    // Tag them with currentLevel_ so the level-ordered saturation places them
    // after all lower-level merges.
    size_t mqTagFrom = mergeQueue_.size();
    if (arrayMode_) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            arrayReasoner_.enqueueEagerMerges(mergeQueue_);
        }
    }
    // Register signatures for all newly interned terms before entering the
    // saturation loop.  This ensures late-interned terms (e.g. f(a) after a=b
    // has already been merged) are visible to congruence detection.
    {
        auto _rt0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                       : std::chrono::steady_clock::time_point{};
        egraph_.registerPendingSignatures(mergeQueue_);
        if (hotProfileEnabled_) hotProfile_.registerSigUs +=
            std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - _rt0).count();
    }
    for (size_t i = mqTagFrom; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = currentLevel_;

    // XOLVER_UF_DISEQ_WATCH: index active disequalities by endpoint term so the
    // saturation loop can check, after each merge, only the disequalities that
    // touch the just-merged class (instead of re-scanning all of them).
    if (diseqWatchEnabled_) {
        rebuildDiseqIndex();
    }

    // Saturation loop, processed in ASCENDING decision-level order so the
    // egraph's size-based undo trail stays level-monotonic (interface-equality
    // merges can be injected out of record order; level order is the invariant
    // backtrack relies on). At each level transition we record an egraph
    // boundary = the state before that level's merges, which backtrack restores.
    int processingLevel = INT_MIN;
    // Process one pending merge at its decision level L. `pushCong` re-enqueues
    // each congruence this merge spawns (tagged with L). Returns nullopt to keep
    // draining, or a TheoryCheckResult to early-return (unknown / conflict).
    // Shared by both drivers below so the two paths are behaviourally identical;
    // only the queue data structure differs.
    auto applyMerge = [&](PendingMerge req, auto&& pushCong)
                          -> std::optional<TheoryCheckResult> {
        const int L = req.level;

        if (egraph_.same(req.a, req.b)) return std::nullopt;

        // sort check
        const auto& na = termManager_.node(req.a);
        const auto& nb = termManager_.node(req.b);
        if (na.sort != nb.sort && na.sort != NullSort && nb.sort != NullSort) {
            pendingUnknown_ = true;
            return TheoryCheckResult::unknown();
        }

        if (L != processingLevel) {
            recordEgraphBoundary(L);
            processingLevel = L;
        }

        // Apply the merge into a fresh side-queue so the congruences it spawns
        // can be tagged with this merge's level before re-entering the queue.
        std::deque<PendingMerge> cong;
        auto mr = egraph_.merge(req.a, req.b, req.reason, cong);
        for (auto& c : cong) { c.level = L; pushCong(std::move(c)); }
        if (!mr.merged) return std::nullopt;

        // Evaluate builtin constants in affected parent terms. Skip entirely
        // when no "#builtin.*" symbol exists (e.g. pure QF_UF): the loop below
        // can never fold anything, and collecting the whole merged-class
        // membership × parents on every merge is otherwise an O(class·parents)
        // cost per merge — a primary cause of the QF_UF scaling cliff.
        if (termManager_.hasBuiltinSymbols()) {
            std::vector<EufTermId> toEval;
            auto addParents = [&](EufTermId t) {
                for (EufTermId p : termManager_.parentsOf(t)) {
                    toEval.push_back(p);
                }
            };
            addParents(req.a);
            addParents(req.b);
            for (EufTermId member : egraph_.classMembers(mr.kept)) {
                addParents(member);
            }
            for (EufTermId member : egraph_.classMembers(mr.killed)) {
                addParents(member);
            }
            std::sort(toEval.begin(), toEval.end());
            toEval.erase(std::unique(toEval.begin(), toEval.end()), toEval.end());
            for (EufTermId p : toEval) {
                tryEvaluateBuiltin(p);
            }
        }

        // ITE metadata：只 enqueue，不递归 merge
        onEclassMerged(mr.kept, mr.killed);
        if (pendingConflict_) {
            return TheoryCheckResult::mkConflict(*pendingConflict_);
        }

        // XOLVER_UF_DISEQ_WATCH: only the members of the loser class (mr.killed)
        // had their representative change to mr.kept, so a disequality can become
        // violated only if one of its endpoint terms lives in that loser class.
        // Check those eagerly — the conflict is reported the moment it forms.
        // explainEquality is sound mid-saturation now (N-O proof forest walks the
        // actual merge path; level-aware backtrack keeps the egraph consistent).
        if (diseqWatchEnabled_) {
            for (EufTermId t : egraph_.classMembers(mr.killed)) {
                auto it = diseqByTerm_.find(t);
                if (it == diseqByTerm_.end()) continue;
                for (const auto& [idx, which] : it->second) {
                    const ActiveDisequality& d =
                        (which == 0) ? disequalities_[idx] : sharedDisequalities_[idx];
                    if (egraph_.same(d.lhs, d.rhs)) {
                        pendingConflict_ = buildDiseqConflict(d);
                        return TheoryCheckResult::mkConflict(*pendingConflict_);
                    }
                }
            }
        }
        // refreshCongruence is now handled inside merge()
        return std::nullopt;
    };

    auto _satT0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                     : std::chrono::steady_clock::time_point{};
    {
    aniaprof::Scope _profSat(aniaprof::EUF_SATURATE);
    if (!minLevelHeapEnabled_) {
        // Baseline: O(n) linear min-level scan + O(n) erase per pop (byte-identical
        // to the historical loop). Congruences append to mergeQueue_.
        while (!mergeQueue_.empty()) {
            // Pick the minimum-level pending merge (earliest at that level).
            size_t mi = 0;
            for (size_t i = 1; i < mergeQueue_.size(); ++i)
                if (mergeQueue_[i].level < mergeQueue_[mi].level) mi = i;
            PendingMerge req = mergeQueue_[mi];
            mergeQueue_.erase(mergeQueue_.begin() + static_cast<long>(mi));
            if (hotProfileEnabled_) ++hotProfile_.mergesProcessed;
            auto r = applyMerge(std::move(req),
                                [&](PendingMerge c) { mergeQueue_.push_back(std::move(c)); });
            if (r) {
                if (hotProfileEnabled_) hotProfile_.saturationUs +=
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        std::chrono::steady_clock::now() - _satT0).count();
                return *r;
            }
        }
    } else {
        // XOLVER_EUF_MINLEVEL_HEAP: level-bucketed drain. begin() is the minimum
        // level; each bucket is FIFO so the per-level order matches the baseline's
        // "earliest at that level". O(n log L) total (L = #distinct levels) vs the
        // baseline's O(n^2). Congruences spawned at level L (the current minimum)
        // re-enter byLevel[L], so they are processed before any higher level —
        // identical ordering to the linear scan's global-min re-pick.
        std::map<int, std::deque<PendingMerge>> byLevel;
        // Absorb any merges sitting in mergeQueue_ into the level buckets. Called
        // initially AND after every applyMerge, because some merges are pushed to
        // mergeQueue_ DIRECTLY (not via pushCong) from inside the merge body —
        // notably tryEvaluateBuiltin's BuiltinEval folds (level 0). The baseline
        // linear scan would re-pick those by global-min; absorbing keeps the map
        // path behaviourally identical and source-agnostic.
        auto absorb = [&]() {
            if (mergeQueue_.empty()) return;
            for (auto& m : mergeQueue_) byLevel[m.level].push_back(std::move(m));
            mergeQueue_.clear();
        };
        absorb();
        auto pushCong = [&](PendingMerge c) { byLevel[c.level].push_back(std::move(c)); };
        while (!byLevel.empty()) {
            auto it = byLevel.begin();
            PendingMerge req = std::move(it->second.front());
            it->second.pop_front();
            if (it->second.empty()) byLevel.erase(it);
            if (hotProfileEnabled_) ++hotProfile_.mergesProcessed;
            auto r = applyMerge(std::move(req), pushCong);
            if (r) {
                if (hotProfileEnabled_) hotProfile_.saturationUs +=
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        std::chrono::steady_clock::now() - _satT0).count();
                return *r;
            }
            absorb();
        }
    }
    }  // end EUF_SATURATE profiling scope
    if (hotProfileEnabled_) hotProfile_.saturationUs +=
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - _satT0).count();

    // true/false conflict
    if (trueTerm_ != NullEufTerm && falseTerm_ != NullEufTerm &&
        egraph_.same(trueTerm_, falseTerm_)) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] TRUE-FALSE-conflict ok=" << er.ok
                      << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF_EXPLAIN_FAIL] true=false same=" << egraph_.same(trueTerm_, falseTerm_)
                      << " activeReasons=" << allActiveReasons().size() << "\n";
        }
        return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
    }

    // disequality conflicts
    for (const auto& d : disequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (std::getenv("EUF_DIAG")) {
                std::cerr << "[EUF-DIAG] diseq-conflict lhs=" << d.lhs << " rhs=" << d.rhs
                          << " ok=" << er.ok << " chain=" << er.reasons.size() << " reasons=";
                for (auto l : er.reasons) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << " diseqReason=" << (d.reason.sign?"":"-") << d.reason.var << "\n";
            }
            if (er.ok) {
                er.reasons.push_back(d.reason);
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            if (std::getenv("EUF_DIAG")) {
                std::cerr << "[EUF_EXPLAIN_FAIL] diseq lhs=" << d.lhs << " rhs=" << d.rhs
                          << " same=" << egraph_.same(d.lhs, d.rhs)
                          << " activeReasons=" << allActiveReasons().size() << "\n";
            }
            auto reasons = allActiveReasons();
            reasons.push_back(d.reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
    }

    // shared disequality conflicts
    for (const auto& d : sharedDisequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (std::getenv("EUF_DIAG")) {
                auto exprOf = [&](EufTermId t) -> int {
                    for (auto& kv : sharedTermToEufTerm_) {
                        if (kv.second == t && sharedTermRegistry_) {
                            const auto* s = sharedTermRegistry_->get(kv.first);
                            if (s) return (int)s->coreExpr;
                        }
                    }
                    return -1;
                };
                auto kindOf = [&](int ex) -> int { return (ex >= 0 && coreIr_) ? (int)coreIr_->get((ExprId)ex).kind : -99; };
                int ea = exprOf(d.lhs), eb = exprOf(d.rhs);
                std::cerr << "[EUF-DIAG] SHARED-DISEQ-conflict lhs=" << d.lhs << "(expr" << ea << ",k" << kindOf(ea) << ")"
                          << " rhs=" << d.rhs << "(expr" << eb << ",k" << kindOf(eb) << ")"
                          << " ok=" << er.ok << " chain=" << er.reasons.size() << " reasons=";
                for (auto l : er.reasons) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << " diseqReason=" << (d.reason.sign?"":"-") << d.reason.var << "\n";
            }
            if (er.ok) {
                er.reasons.push_back(d.reason);
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            auto reasons = allActiveReasons();
            reasons.push_back(d.reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
    }

#ifndef NDEBUG
    assert(mergeQueue_.empty());
    assert(egraph_.congruenceClosed());
#endif

    // Datatype clash / acyclicity conflicts. Sound UNSAT detection against the
    // now-congruence-closed egraph; safe at any effort (a hard contradiction).
    if (dtMode_) {
        ensureDtContext();
        if (dtReasoner_.active()) {
            if (auto conflict = dtReasoner_.checkConflict()) {
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(*conflict)});
            }
        }
    }

    // Array Row2/Extensionality lemmas — emitted only at Full effort (complete
    // SAT model), so the case split is over a stable assignment. The lemma
    // literals are observed dynamic equality atoms; returning Lemma lets the
    // SAT solver branch on them and re-enter check().
    if (arrayMode_ && effort == TheoryEffort::Full) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            auto diseqs = activeArrayDiseqs();
            auto lemma = arrayReasoner_.instantiateLemma(diseqs);
            if (lemma && !lemma->empty()) {
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                // Only emit if genuinely new; otherwise the same lemma would
                // be regenerated forever (the dedup caches already gate this,
                // but guard against a re-derivation across solver instances).
                if (!lemmaDb.contains(tl)) {
                    return TheoryCheckResult::mkLemma(std::move(tl));
                }
            }
        }
    }

    // Datatype injectivity / guarded-projection / exhaustiveness-split /
    // reconstruction lemmas (full effort). These propagate implied field
    // equalities, force a constructor choice for an observed class, or rebuild a
    // term from a decided tester — feeding back through the SAT core and
    // surfacing clash/diseq conflicts (e.g. finite cardinality).
    if (dtMode_ && effort == TheoryEffort::Full) {
        ensureDtContext();
        if (dtReasoner_.active()) {
            auto lemma = dtReasoner_.instantiateLemma();
            if (lemma && !lemma->empty()) {
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                if (!lemmaDb.contains(tl)) {
                    return TheoryCheckResult::mkLemma(std::move(tl));
                }
            }
        }
    }

    // Datatype completeness gate (the authoritative DT sat gate — satComplete is
    // not consulted on the single-theory path). A sat is sound only when every
    // OBSERVED datatype class (selector-read / decided-tester / finite-sort) has
    // a determined constructor, i.e. the DT structure is a concrete ground-term
    // model. Otherwise return Unknown: the propagator turns a Full-effort Unknown
    // into a sound `unknown` verdict rather than an unvalidated sat.
    if (dtMode_ && effort == TheoryEffort::Full) {
        ensureDtContext();
        if (dtReasoner_.active() && !dtReasoner_.modelFullyDetermined()) {
            return TheoryCheckResult::unknown(
                "dt: model not fully determined (observed datatype class has no constructor)");
        }
        // DT model re-validator: evaluate every original assertion under the
        // live e-graph. Catches false-SATs where modelFullyDetermined accepts
        // (every observed class has SOME ctor) but a deep BMC encoding
        // (ITE-chain over testers/selectors) is actually violated. SMT-LIB-
        // strict semantics: selector-on-wrong-ctor is Indeterminate, not
        // Violated — never over-rejects sat cases like `(head nil) = red`.
        // Default ON; XOLVER_DT_VALIDATE_OFF=1 disables (A/B escape).
        static const bool dtValidateOff =
            std::getenv("XOLVER_DT_VALIDATE_OFF") != nullptr;
        if (!dtValidateOff && dtReasoner_.active() && coreIr_ &&
            originalAssertionsForDtValidate_ &&
            !originalAssertionsForDtValidate_->empty()) {
            DtModelValidator v(*coreIr_, termManager_, egraph_, coreIr_->datatypes());
            // Strict mode: floor on Indeterminate too. Master 5min batch
            // surfaced 43 false-SATs the lenient default missed (the e-graph
            // arrived at a sat verdict without enough constructor witnesses
            // for structural eval to ground out). Sound but may over-floor
            // true-sat opaque-DT cases. See validator header.
            static const bool dtValidatorStrict =
                std::getenv("XOLVER_DT_VALIDATOR_STRICT") != nullptr;
            v.setStrictMode(dtValidatorStrict);
            auto verdict = v.validate(*originalAssertionsForDtValidate_);
            if (std::getenv("XOLVER_DT_VALIDATE_DIAG")) {
                std::cerr << "[DT-VAL] assertions=" << originalAssertionsForDtValidate_->size()
                          << " verdict=" << (verdict == DtModelValidator::Verdict::Satisfied ? "Sat"
                                          : verdict == DtModelValidator::Verdict::Violated ? "Violated"
                                          : "Indeterminate") << "\n";
            }
            if (verdict == DtModelValidator::Verdict::Violated) {
                return TheoryCheckResult::unknown(
                    "dt: candidate model violates an original assertion "
                    "(DtModelValidator re-evaluation Violated; sound floor)");
            }
        }
    }

    // Capture the array/scalar model NOW, while the egraph reflects this
    // satisfying assignment. After solve() returns, the egraph is rolled back
    // and select/bridge merges are lost, so getModel() reads this snapshot.
    // Only at Full effort (a complete model check) is the state authoritative.
    if ((arrayMode_ || (ufModelEnabled_ && sharedTermRegistry_)) &&
        effort == TheoryEffort::Full) {
        modelSnapshot_ = buildModel();
    }

    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks
// ---------------------------------------------------------------------------

EufTermId EufSolver::internSharedConstant(SharedTermId s) {
    auto it = sharedTermToEufTerm_.find(s);
    if (it != sharedTermToEufTerm_.end()) {
        return it->second;
    }

    if (!sharedTermRegistry_ || !coreIr_) return NullEufTerm;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return NullEufTerm;

    EufTermId t = termManager_.intern(st->coreExpr, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        sharedTermToEufTerm_[s] = t;
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

EufTermId EufSolver::internEufExpr(ExprId eid) {
    if (!coreIr_) return NullEufTerm;
    EufTermId t = termManager_.intern(eid, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

TheoryCheckResult EufSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    currentLevel_ = std::max(currentLevel_, level);
    size_t mqBefore = mergeQueue_.size();
    auto tagFromHere = [&]() {
        for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    };

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        tagFromHere();
        return TheoryCheckResult::unknown();
    }

    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.lit = reason;
    mergeQueue_.push_back({ta, tb, mr});
    tagFromHere();
    return TheoryCheckResult::consistent();
}

TheoryCheckResult EufSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    currentLevel_ = std::max(currentLevel_, level);
    size_t mqBefore = mergeQueue_.size();

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::unknown();
    }

    if (egraph_.same(ta, tb)) {
        auto er = egraph_.explainEquality(ta, tb);
        if (std::getenv("EUF_DIAG")) {
            const auto* sa = sharedTermRegistry_ ? sharedTermRegistry_->get(a) : nullptr;
            const auto* sb = sharedTermRegistry_ ? sharedTermRegistry_->get(b) : nullptr;
            auto dump = [&](const char* tag, auto s) {
                std::cerr << " " << tag << "{";
                if (s && coreIr_) {
                    const auto& e = coreIr_->get(s->coreExpr);
                    std::cerr << "expr=" << (int)s->coreExpr << " kind=" << (int)e.kind;
                    if (auto* iv = std::get_if<int64_t>(&e.payload.value)) std::cerr << " int=" << *iv;
                    else if (auto* sv = std::get_if<std::string>(&e.payload.value)) std::cerr << " sym=" << *sv;
                    std::cerr << " nch=" << e.children.size();
                }
                std::cerr << "}";
            };
            std::cerr << "[EUF-DIAG] IFACE-DISEQ-IMMEDIATE sharedA=" << a << " sharedB=" << b
                      << " ta=" << ta << " tb=" << tb << " sameSharedId=" << (a == b);
            dump("A", sa); dump("B", sb);
            std::cerr << " ok=" << er.ok << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
            er.reasons.push_back(reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        auto reasons = allActiveReasons();
        reasons.push_back(reason);
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    }

    sharedDisequalities_.push_back({ta, tb, reason, level, trail_.size()});
    return TheoryCheckResult::consistent();
}

bool EufSolver::areSharedTermsMerged(SharedTermId a, SharedTermId b) const {
    if (a == b) return true;
    // Only consult terms that have ALREADY been interned as shared constants.
    // Interning is a mutating operation (registers signatures / enqueues
    // merges), so a const observer must not trigger it. If a shared scalar has
    // never been interned, it cannot be merged with anything on the EUF side
    // yet -> report not-merged (conservative).
    auto ia = sharedTermToEufTerm_.find(a);
    auto ib = sharedTermToEufTerm_.find(b);
    if (ia == sharedTermToEufTerm_.end() || ib == sharedTermToEufTerm_.end())
        return false;
    if (ia->second == NullEufTerm || ib->second == NullEufTerm) return false;
    return egraph_.same(ia->second, ib->second);
}

std::vector<TheorySolver::SharedEqualityPropagation>
EufSolver::getDeducedSharedEqualities() {
    std::vector<SharedEqualityPropagation> result;
    if (!sharedTermRegistry_) return result;

    const auto& allShared = sharedTermRegistry_->allSharedTerms();
    for (size_t i = 0; i < allShared.size(); ++i) {
        EufTermId ti = internSharedConstant(allShared[i]);
        if (ti == NullEufTerm) continue;
        for (size_t j = i + 1; j < allShared.size(); ++j) {
            EufTermId tj = internSharedConstant(allShared[j]);
            if (tj == NullEufTerm) continue;
            // Care-graph prune (XOLVER_COMB_CAREGRAPH): skip pairs no theory
            // cares about. Done AFTER interning (so egraph state is identical
            // to the unpruned path) but before the expensive same/explain. An
            // EUF-merged pair is always care-relevant (it was connected via an
            // Eq/Distinct or a congruence arg), so this prunes only inert,
            // never-equal pairs — no real propagation is lost.
            if (careGraph_ && !careGraph_->caresPair(allShared[i], allShared[j]))
                continue;
            if (egraph_.same(ti, tj)) {
                auto er = egraph_.explainEquality(ti, tj);
                if (er.ok) {
                    result.push_back({allShared[i], allShared[j], std::move(er.reasons)});
                }
            }
        }
    }

    return result;
}

std::optional<TheorySolver::TheoryModel> EufSolver::getModel() const {
    // The array/scalar model must be read off the egraph WHILE it reflects the
    // satisfying assignment. By the time the Solver calls getModel() (after
    // solve() returns), the egraph has been rolled back, so select/bridge
    // merges no longer hold. We therefore return the snapshot captured at the
    // last consistent Full-effort check. Fall back to a live build only if no
    // snapshot exists (defensive — e.g. a non-array EUF problem).
    if (modelSnapshot_) return modelSnapshot_;
    return buildModel();
}

// Canonical class token in the ArithModelValidator's namespaced form so the
// validator's asToken() and these tokens compare identically:
//   numeric literal  -> "#n:<canonical-rational>"
//   bool literal      -> "#b:1" / "#b:0"
//   otherwise         -> opaque per-class marker "@e<rep>"
// Index/element sorts may be uninterpreted; equality-by-token is exactly the
// QF_AX semantics (and, for Track 3, the UF argument/value identity).
std::string EufSolver::classToken(EufTermId t) const {
    if (t == NullEufTerm) return "@nil";
    EClassId rep = egraph_.rep(t);
    for (EufTermId m : egraph_.classMembers(rep)) {
        const auto& mn = termManager_.node(m);
        if (mn.origin == NullExpr) continue;
        if (mn.origin == TrueSentinelExpr || mn.origin == FalseSentinelExpr) continue;
        const auto& e = coreIr_->get(mn.origin);
        if (e.isConst()) {
            if (auto* i = std::get_if<int64_t>(&e.payload.value))
                return "#n:" + mpq_class(*i).get_str();
            if (auto* b = std::get_if<bool>(&e.payload.value))
                return std::string("#b:") + (*b ? "1" : "0");
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                // Numeric literal stored as string (Int/Real const).
                try { return "#n:" + mpq_class(*s).get_str(); } catch (...) {}
                return *s;
            }
        }
    }
    return "@e" + std::to_string(rep);
}

std::string EufSolver::sortName(SortId s) const {
    auto sk = coreIr_->sortKind(s);
    if (sk == SortKind::Int) return "Int";
    if (sk == SortKind::Real) return "Real";
    if (sk == SortKind::Bool) return "Bool";
    return "U" + std::to_string(s);
}

std::optional<TheorySolver::TheoryModel> EufSolver::buildModel() const {
    if (!coreIr_) return std::nullopt;
    TheoryModel model;
    if (arrayMode_) buildArrayModel(model);
    // Track 3: token-keyed UF interps for combination model validation. Scoped
    // to combination (sharedTermRegistry_); pure QF_UF gets them from CMS.
    if (ufModelEnabled_ && sharedTermRegistry_) collectFunctionInterps(model);
    if (model.arrayInterps.empty() && model.functionInterps.empty() &&
        model.assignments.empty() && model.numericAssignments.empty())
        return std::nullopt;
    return model;
}

void EufSolver::buildArrayModel(TheoryModel& model) const {
    if (!arrayMode_ || !coreIr_) return;

    // Group array variables by eclass so equal arrays share one interp.
    // Identify array variables in the CoreIr (Variable nodes with array sort).
    struct ArrBuild {
        std::string defaultVal;
        bool hasConstDefault = false;
        std::string indexSort, elemSort;
        // index-token -> value-token, plus the index-class rep used for dedup.
        std::vector<std::pair<std::string, std::string>> entries;
        std::unordered_set<EClassId> seenIdxClass;
    };
    std::unordered_map<EClassId, ArrBuild> byClass;

    // Collect every array variable EufTermId.
    std::vector<std::pair<std::string, EufTermId>> arrayVars;
    for (ExprId id = 0; id < static_cast<ExprId>(coreIr_->size()); ++id) {
        const auto& e = coreIr_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (!coreIr_->arraySortParams(e.sort)) continue;
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        // Intern is monotonic; the term should already exist if it was used.
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<CoreIr&>(*coreIr_));
        if (t == NullEufTerm) continue;
        arrayVars.push_back({std::get<std::string>(e.payload.value), t});
    }
    if (arrayVars.empty()) return;

    // Seed an ArrBuild per array class, recording sorts + const default.
    for (const auto& [name, t] : arrayVars) {
        EClassId rep = egraph_.rep(t);
        auto& ab = byClass[rep];
        const auto& tn = termManager_.node(t);
        if (auto params = coreIr_->arraySortParams(tn.sort)) {
            ab.indexSort = sortName(params->first);
            ab.elemSort = sortName(params->second);
        }
        // const default if the class contains a const-array.
        if (!ab.hasConstDefault) {
            for (EufTermId m : egraph_.classMembers(rep)) {
                if (arrayReasoner_.isConstArray(m)) {
                    const auto& cn = termManager_.node(m);
                    if (cn.args.size() == 1) {
                        ab.defaultVal = classToken(cn.args[0]);
                        ab.hasConstDefault = true;
                    }
                    break;
                }
            }
        }
    }

  if (!storeModelEnabled_) {
    // Populate entries from select terms. select(arr,idx): the arr-class gets
    // an entry idx-token -> value-token where value = the select term's class.
    for (EufTermId sel : arrayReasoner_.selectTerms()) {
        const auto& sn = termManager_.node(sel);
        if (sn.args.size() != 2) continue;
        EClassId arrRep = egraph_.rep(sn.args[0]);
        auto it = byClass.find(arrRep);
        if (it == byClass.end()) continue;  // select on a non-variable class
        EClassId idxRep = egraph_.rep(sn.args[1]);
        if (!it->second.seenIdxClass.insert(idxRep).second) continue;
        it->second.entries.push_back({classToken(sn.args[1]), classToken(sel)});
    }

    // Assign a per-class default token when no const was found. Distinct
    // classes get distinct defaults so two unconstrained arrays differ at any
    // index not pinned by a shared read (defense; disequalities are also
    // witnessed by Ext read indices).
    for (auto& [rep, ab] : byClass) {
        if (!ab.hasConstDefault) {
            ab.defaultVal = "@def" + std::to_string(rep);
        }
    }
  } else {
    // ---- Store-aware construction (XOLVER_AX_STORE_MODEL) -------------------
    // Reads keyed by array class: (index-class, index-token, value-token).
    std::unordered_map<EClassId,
        std::vector<std::tuple<EClassId, std::string, std::string>>> readsByClass;
    for (EufTermId sel : arrayReasoner_.selectTerms()) {
        const auto& sn = termManager_.node(sel);
        if (sn.args.size() != 2) continue;
        EClassId arrRep = egraph_.rep(sn.args[0]);
        readsByClass[arrRep].push_back(
            {egraph_.rep(sn.args[1]), classToken(sn.args[1]), classToken(sel)});
    }
    struct Interp {
        std::string deflt;
        // index-class -> (index-token, value-token). Override semantics: a later
        // write at the same index class replaces the inherited entry.
        std::map<EClassId, std::pair<std::string, std::string>> ovr;
    };
    std::unordered_map<EClassId, Interp> memo;
    std::unordered_set<EClassId> active;  // cycle guard (stores are acyclic)
    std::function<Interp(EClassId)> build = [&](EClassId rep) -> Interp {
        auto mit = memo.find(rep);
        if (mit != memo.end()) return mit->second;
        Interp self;
        if (!active.insert(rep).second) {            // defensive: break a cycle
            self.deflt = "@def" + std::to_string(rep);
            memo[rep] = self;
            return self;
        }
        // Pick a generator in the class: const-array (sets default) else a store.
        EufTermId cMem = NullEufTerm, sMem = NullEufTerm;
        for (EufTermId m : egraph_.classMembers(rep)) {
            if (arrayReasoner_.isConstArray(m)) { if (cMem == NullEufTerm) cMem = m; }
            else if (arrayReasoner_.isStore(m)) { if (sMem == NullEufTerm) sMem = m; }
        }
        if (cMem != NullEufTerm) {
            const auto& cn = termManager_.node(cMem);
            if (cn.args.size() == 1) self.deflt = classToken(cn.args[0]);
        } else if (sMem != NullEufTerm) {
            const auto& stn = termManager_.node(sMem);
            if (stn.args.size() == 3) {
                Interp base = build(egraph_.rep(stn.args[0]));  // recurse on base
                self.deflt = base.deflt;
                self.ovr = std::move(base.ovr);                 // inherit entries
                self.ovr[egraph_.rep(stn.args[1])] =            // apply this write
                    {classToken(stn.args[1]), classToken(stn.args[2])};
            }
        }
        if (self.deflt.empty()) self.deflt = "@def" + std::to_string(rep);  // leaf
        // Overlay explicit reads on THIS class (non-write indices + confirmation).
        // Do not overwrite an inherited/own store write at the same index class.
        auto rit = readsByClass.find(rep);
        if (rit != readsByClass.end())
            for (const auto& [ic, itok, vtok] : rit->second)
                if (self.ovr.find(ic) == self.ovr.end()) self.ovr[ic] = {itok, vtok};
        active.erase(rep);
        memo[rep] = self;
        return self;
    };
    for (auto& [rep, ab] : byClass) {
        Interp it = build(rep);
        ab.defaultVal = it.deflt;
        ab.entries.clear();
        for (const auto& [ic, pr] : it.ovr) ab.entries.push_back(pr);
    }
  }

    // Emit one ArrayInterp per array variable (sharing the class build).
    for (const auto& [name, t] : arrayVars) {
        EClassId rep = egraph_.rep(t);
        auto it = byClass.find(rep);
        if (it == byClass.end()) continue;
        TheoryModel::ArrayInterp ai;
        ai.indexSort = it->second.indexSort;
        ai.elemSort = it->second.elemSort;
        ai.defaultVal = it->second.defaultVal;
        ai.entries = it->second.entries;
        model.arrayInterps[name] = std::move(ai);
    }

    if (model.arrayInterps.empty()) return;

    // Scalar token assignments for every non-array, non-bool variable that the
    // egraph knows about (index/element vars). The validator needs these to
    // evaluate select/store; tokens are the same class tokens used in the
    // array interps, so they stay consistent. Bool vars stay in `assignments`
    // as "true"/"false"; numeric literals stay numeric.
    for (ExprId id = 0; id < static_cast<ExprId>(coreIr_->size()); ++id) {
        const auto& e = coreIr_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (coreIr_->arraySortParams(e.sort)) continue;  // arrays handled above
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        const std::string& name = std::get<std::string>(e.payload.value);
        if (model.assignments.count(name)) continue;
        // Only emit if the variable was actually interned (used in a term).
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<CoreIr&>(*coreIr_));
        if (t == NullEufTerm) continue;
        auto sk = coreIr_->sortKind(e.sort);
        if (sk == SortKind::Bool) {
            // Resolve against the true/false classes if forced; else default.
            if (trueTerm_ != NullEufTerm && egraph_.same(t, trueTerm_))
                model.assignments[name] = "true";
            else if (falseTerm_ != NullEufTerm && egraph_.same(t, falseTerm_))
                model.assignments[name] = "false";
            continue;
        }
        model.assignments[name] = classToken(t);
    }
}

void EufSolver::collectFunctionInterps(TheoryModel& model) const {
    if (!coreIr_) return;

    // One FuncInterp per uninterpreted function symbol, keyed on the argument
    // CLASS TOKENS (canonical "#n:.."/"#b:.."/"@e.." form). Congruence closure
    // guarantees the table is a genuine function: two applications whose args
    // lie in the same classes are themselves congruent (same class), so they
    // produce identical arg-token tuples AND identical value tokens. The only
    // way the post-remap table (TheoryManager::getModel) could become
    // inconsistent is two DISTINCT classes collapsing to one arith number; the
    // remap's @CONFLICT guard + the per-function consistency check there reject
    // that, so an unsound interp is dropped (-> validator Indeterminate -> floor)
    // rather than confirming a wrong model.
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        const auto& n = termManager_.node(t);
        if (n.args.empty()) continue;            // not an application
        if (n.origin == NullExpr) continue;
        const auto& oe = coreIr_->get(n.origin);
        if (oe.kind != Kind::UFApply) continue;  // only genuine UF applications
        if (!std::holds_alternative<std::string>(oe.payload.value)) continue;
        const std::string& fname = std::get<std::string>(oe.payload.value);

        auto& fi = model.functionInterps[fname];
        if (fi.argSorts.empty() && !n.args.empty()) {
            for (EufTermId a : n.args)
                fi.argSorts.push_back(sortName(termManager_.node(a).sort));
            fi.retSort = sortName(n.sort);
            // Empty default: a tuple absent from the table -> the validator's
            // UFApply lookup sees an empty value -> Indeterminate (sound floor),
            // never a guessed value. Every UFApply in the ground assertions was
            // interned, so the table is complete for what the validator evaluates.
            fi.deflt = "";
        }
        TheoryModel::FuncEntry entry;
        entry.args.reserve(n.args.size());
        for (EufTermId a : n.args) entry.args.push_back(classToken(a));
        entry.value = classToken(t);
        bool dup = false;
        for (const auto& ex : fi.entries)
            if (ex.args == entry.args) { dup = true; break; }
        if (!dup) fi.entries.push_back(std::move(entry));
    }

    if (model.functionInterps.empty()) return;

    // Emit scalar var -> class-token assignments for every interned, non-array,
    // non-bool variable the egraph knows (incl. purification vars that appear as
    // UF arguments). TheoryManager::getModel pairs these tokens with the arith
    // model's numeric value to remap the function-interp arg/value tokens to the
    // bare rationals the validator expects. (Same mechanism the array path uses.)
    for (ExprId id = 0; id < static_cast<ExprId>(coreIr_->size()); ++id) {
        const auto& e = coreIr_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (coreIr_->arraySortParams(e.sort)) continue;
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        const std::string& name = std::get<std::string>(e.payload.value);
        if (model.assignments.count(name)) continue;
        EufTermId t = termManager_.findTerm(id);
        if (t == NullEufTerm) continue;
        auto sk = coreIr_->sortKind(e.sort);
        if (sk == SortKind::Bool) {
            if (trueTerm_ != NullEufTerm && egraph_.same(t, trueTerm_))
                model.assignments[name] = "true";
            else if (falseTerm_ != NullEufTerm && egraph_.same(t, falseTerm_))
                model.assignments[name] = "false";
            continue;
        }
        model.assignments[name] = classToken(t);
    }
}

void EufSolver::tryEvaluateBuiltin(EufTermId t) {
    if (!coreIr_) return;
    const auto& node = termManager_.node(t);
    if (node.args.empty()) return;

    std::string symName = termManager_.symbolName(node.symbol);
    if (symName.empty() || symName[0] != '#') return;

    // Collect constant argument values from the equivalence class of each arg.
    // Also record, per arg, the CONSTANT MEMBER term that supplied the value:
    // the merge "t = eval(args)" is justified by each arg being equal to that
    // constant (e.g. x+1 = 2 holds because x = 1). Capturing (arg, constMember)
    // lets explainEquality recurse into explain(arg ≡ constMember) and reach the
    // base literals — without it the BuiltinEval merge carried an empty reason,
    // producing an INCOMPLETE conflict explanation (false-UNSAT / stale-merge
    // dependency hidden from conflict analysis).
    std::vector<mpq_class> values;
    std::vector<std::pair<EufTermId, EufTermId>> argConstPairs;
    values.reserve(node.args.size());
    argConstPairs.reserve(node.args.size());
    for (EufTermId arg : node.args) {
        EClassId cid = egraph_.rep(arg);
        bool found = false;
        mpq_class val;
        EufTermId constMember = NullEufTerm;
        for (EufTermId member : egraph_.classMembers(cid)) {
            const auto& mnode = termManager_.node(member);
            if (mnode.origin == NullExpr) continue;
            const auto& expr = coreIr_->get(mnode.origin);
            if (!expr.isConst()) continue;
            if (auto* i = std::get_if<int64_t>(&expr.payload.value)) {
                val = mpq_class(*i);
                found = true;
                constMember = member;
                break;
            } else if (auto* s = std::get_if<std::string>(&expr.payload.value)) {
                try {
                    val = mpq_class(*s);
                    found = true;
                    constMember = member;
                    break;
                } catch (...) {
                    continue;
                }
            }
        }
        if (!found) return;
        values.push_back(val);
        argConstPairs.push_back({arg, constMember});
    }

    mpq_class result;
    bool ok = false;
    if (symName == "#builtin.Add") {
        if (values.size() != 2) return;
        result = values[0] + values[1];
        ok = true;
    } else if (symName == "#builtin.Sub") {
        if (values.size() != 2) return;
        result = values[0] - values[1];
        ok = true;
    } else if (symName == "#builtin.Neg") {
        if (values.size() != 1) return;
        result = -values[0];
        ok = true;
    } else if (symName == "#builtin.Mul") {
        if (values.size() != 2) return;
        result = values[0] * values[1];
        ok = true;
    } else if (symName == "#builtin.Div") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        result = values[0] / values[1];
        ok = true;
    } else if (symName == "#builtin.Mod") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        // mpq_class doesn't have mod; use integer mod if both are integers
        if (values[0].get_den() == 1 && values[1].get_den() == 1) {
            mpz_class r = values[0].get_num() % values[1].get_num();
            result = mpq_class(r);
            ok = true;
        }
    } else if (symName == "#builtin.Abs") {
        if (values.size() != 1) return;
        result = abs(values[0]);
        ok = true;
    }

    if (!ok) return;

    std::string resultStr = result.get_str();
    EufTermId constTerm = termManager_.internConstant(resultStr, node.sort);
    if (constTerm != NullEufTerm && !egraph_.same(t, constTerm)) {
        MergeReason mr;
        mr.kind = MergeReasonKind::BuiltinEval;
        mr.lit = SatLit();
        // Explanation = why each arg equals its constant. explainEquality folds a
        // non-AssertedEquality edge by recursing on argPairs, so populating them
        // makes the BuiltinEval merge's explanation complete (reaches the base
        // literals that fixed the args to constants).
        mr.argPairs = std::move(argConstPairs);
        mergeQueue_.push_back({t, constTerm, mr});
    }
}

} // namespace xolver
