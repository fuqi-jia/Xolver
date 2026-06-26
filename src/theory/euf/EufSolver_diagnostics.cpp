#include <cstdlib>
#include "util/EnvParam.h"
#include <chrono>
#include "theory/euf/EufSolver.h"
#include "util/SolveClock.h"
#include <stdexcept>
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

// NOTE: This translation unit was split out of EufSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

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
    // In combination this is drained only under XOLVER_EUF_PROP_COMB (the upstream
    // TheoryManager allow-list gate); the EUF Eq-atom entailments here are sound
    // by construction (¬reasons ∨ implied is an EUF tautology) in either mode.
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
        return static_cast<size_t>(
            std::max(0, env::paramInt("XOLVER_EUF_PROP_BUDGET", 512)));
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
    checkProofForestInvariants("buildDiseqConflict-enter");
    auto er = egraph_.explainEquality(d.lhs, d.rhs);
    std::vector<SatLit> reasons = er.ok ? std::move(er.reasons) : allActiveReasons();
    reasons.push_back(d.reason);
#ifdef XOLVER_ENABLE_PROOFS
    // Push an eq_transitive certificate only when the explanation succeeded (a
    // clean equality chain). The Solver's union-find self-check keeps just the
    // pure-transitivity ones.
    if (er.ok) pushEufTransitivityCert(reasons);
#endif
    return TheoryConflict{std::move(reasons)};
}

bool EufSolver::checkProofForestInvariants(const char* where) const {
    const bool diag = xolver::env::diag("XOLVER_DIAG_PF_INV");
    const bool doAssert = xolver::env::diag("XOLVER_ASSERT_PF_INV");
    if (!diag && !doAssert) return true;

    // "Currently asserted literal" must be sourced from BOTH:
    //   - trail_: assertLit-driven assertions (theory atoms decided by SAT)
    //   - mergeRecords_: combination interface (dis)equality reasons (assert
    //     InterfaceEquality/Disequality bypasses trail_ entirely and stores
    //     the reason in the merge record's MergeReason).
    // Without including mergeRecords_, every interface-eq edge in proof forest
    // would be falsely flagged "stale" since its reason literal isn't in
    // trail_. The pair (trail_ + mergeRecord reasons) is the complete set of
    // literals EUF observed as asserted.
    auto litKey = [](SatLit l) {
        return (static_cast<uint64_t>(l.var) << 1) | (l.sign ? 1u : 0u);
    };
    std::unordered_set<uint64_t> trailLits;
    for (const auto& e : trail_) trailLits.insert(litKey(e.lit));
    for (size_t i = 0; i < egraph_.mergeRecordCount(); ++i) {
        const auto& mr = egraph_.mergeRecord(i);
        if (mr.reason.kind == MergeReasonKind::AssertedEquality &&
            mr.reason.lit.var != 0) {
            trailLits.insert(litKey(mr.reason.lit));
        }
    }
    for (const auto& d : sharedDisequalities_) trailLits.insert(litKey(d.reason));
    for (const auto& d : disequalities_)       trailLits.insert(litKey(d.reason));

    const ProofForest& pf = egraph_.proofForest();
    const size_t n = pf.nodeCount();
    int violations = 0;

    for (EufTermId t = 0; t < static_cast<EufTermId>(n); ++t) {
        EufTermId p = pf.parentOf(t);
        if (p == t) continue;  // root has no outgoing edge
        size_t lid = pf.labelIdxOf(t);
        const MergeReason& r = pf.edgeReason(lid);
        switch (r.kind) {
            case MergeReasonKind::AssertedEquality: {
                if (!trailLits.count(litKey(r.lit))) {
                    if (diag) {
                        std::fprintf(stderr,
                            "[PF-INV][%s] STALE AssertedEquality edge t=%u -> %u "
                            "label_idx=%zu reason=%c%d NOT on trail (level=%d)\n",
                            where, t, p, lid,
                            r.lit.sign ? '+' : '-', r.lit.var, currentLevel_);
                    }
                    ++violations;
                    if (doAssert) std::abort();
                }
                // Polarity-opposite literal present on trail = catastrophic.
                SatLit opp{r.lit.var, !r.lit.sign};
                if (trailLits.count(litKey(opp))) {
                    if (diag) {
                        std::fprintf(stderr,
                            "[PF-INV][%s] POLARITY-CONFLICT edge t=%u -> %u "
                            "label has %c%d but trail has %c%d (level=%d)\n",
                            where, t, p, r.lit.sign ? '+' : '-', r.lit.var,
                            opp.sign ? '+' : '-', opp.var, currentLevel_);
                    }
                    ++violations;
                    if (doAssert) std::abort();
                }
                break;
            }
            case MergeReasonKind::Congruence: {
                // Each argPair must currently be same-class in the egraph.
                for (const auto& [a, b] : r.argPairs) {
                    if (!egraph_.same(a, b)) {
                        if (diag) {
                            // Dump the actual EUF term structure for a and b
                            // to expose interning subtlety (e.g. distinct
                            // EufTermIds for the same logical bridge).
                            auto dumpTerm = [&](EufTermId tid) {
                                if (tid >= termManager_.termCount()) { std::fprintf(stderr, "<oob>"); return; }
                                const auto& nd = termManager_.node(tid);
                                std::fprintf(stderr, "%s",
                                    termManager_.symbolName(nd.symbol).c_str());
                                if (!nd.args.empty()) {
                                    std::fprintf(stderr, "(");
                                    for (size_t i = 0; i < nd.args.size(); ++i) {
                                        if (i) std::fprintf(stderr, ",");
                                        std::fprintf(stderr, "%u", nd.args[i]);
                                    }
                                    std::fprintf(stderr, ")");
                                }
                            };
                            std::fprintf(stderr,
                                "[PF-INV][%s] STALE Congruence edge t=%u -> %u "
                                "label_idx=%zu argPair (%u,%u) NOT same-class "
                                "(mergeRecordCount=%zu curLevel=%d)\n",
                                where, t, p, lid, a, b, egraph_.mergeRecordCount(),
                                currentLevel_);
                            std::fprintf(stderr, "  a=%u: ", a); dumpTerm(a);
                            std::fprintf(stderr, "  rep(a)=%u\n", egraph_.rep(a));
                            std::fprintf(stderr, "  b=%u: ", b); dumpTerm(b);
                            std::fprintf(stderr, "  rep(b)=%u\n", egraph_.rep(b));
                            // Also dump b's children (likely Add args) to see
                            // if any of them are constants / folded.
                            if (b < termManager_.termCount()) {
                                const auto& nd = termManager_.node(b);
                                for (size_t ci = 0; ci < nd.args.size(); ++ci) {
                                    EufTermId arg = nd.args[ci];
                                    std::fprintf(stderr, "    b.arg[%zu]=%u: ", ci, arg);
                                    dumpTerm(arg);
                                    std::fprintf(stderr, "  rep=%u\n", egraph_.rep(arg));
                                }
                            }
                        }
                        ++violations;
                        if (doAssert) std::abort();
                        break;
                    }
                }
                break;
            }
            case MergeReasonKind::ArrayRow2Cond: {
                // Conditional Row2: the diseq reason literal must be on the trail
                // (or a recorded diseq reason — both folded into trailLits), and
                // the equality chains in argPairs must currently be same-class.
                if (r.lit.var != 0 && !trailLits.count(litKey(r.lit))) {
                    if (diag) {
                        std::fprintf(stderr,
                            "[PF-INV][%s] STALE ArrayRow2Cond diseq lit %c%d NOT on trail "
                            "(t=%u->%u level=%d)\n", where,
                            r.lit.sign ? '+' : '-', r.lit.var, t, p, currentLevel_);
                    }
                    ++violations;
                    if (doAssert) std::abort();
                }
                for (const auto& [a, b] : r.argPairs) {
                    if (!egraph_.same(a, b)) {
                        if (diag) {
                            std::fprintf(stderr,
                                "[PF-INV][%s] STALE ArrayRow2Cond argPair (%u,%u) NOT "
                                "same-class (t=%u->%u level=%d)\n", where, a, b, t, p,
                                currentLevel_);
                        }
                        ++violations;
                        if (doAssert) std::abort();
                        break;
                    }
                }
                break;
            }
            case MergeReasonKind::BuiltinEval:
            case MergeReasonKind::ArrayRow1:
            case MergeReasonKind::ArrayConst:
            case MergeReasonKind::ArrayRow2:
                // Tautological theory axiom merges contribute no literal; their
                // soundness depends on the axiom holding unconditionally (true
                // for Row1/Row2/Const) or on argPairs (BuiltinEval — verified
                // recursively by the explainEquality walk, not here).
                break;
        }
    }
    if (diag && violations > 0) {
        std::fprintf(stderr, "[PF-INV][%s] TOTAL VIOLATIONS=%d (nodes=%zu)\n",
                     where, violations, n);
    }
    return violations == 0;
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

} // namespace xolver
