#include "theory/euf/IncrementalEGraph.h"
#include <cassert>
#include <algorithm>
#include <queue>
#include <iostream>
#include <cstdlib>

namespace xolver {

IncrementalEGraph::IncrementalEGraph(EufTermManager& tm) : tm_(tm) {
    // fastMerge_ defaults ON (see header). Env =0 disables (A/B escape).
    if (const char* e = std::getenv("XOLVER_UF_FAST_CC")) {
        fastMerge_ = !(e[0] == '0' && e[1] == '\0');
    }
}

void IncrementalEGraph::clear() {
    uf_ = RollbackUnionFind();
    members_.clear();
    memberTrail_.clear();
    mergeRecords_.clear();
    sigTable_.clear();
    currentSig_.clear();
    currentSigTrail_.clear();
    proofForest_.clear();
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;
    nextTermToRegister_ = 0;
}

void IncrementalEGraph::ensureNodeAllocated(EufTermId t) {
    if (t >= members_.size()) {
        size_t oldSize = members_.size();
        members_.resize(t + 1);
        for (size_t i = oldSize; i <= t; ++i) {
            uf_.addNode();
            members_[i].push_back(static_cast<EufTermId>(i));
        }
    }
    if (t >= currentSig_.size()) {
        currentSig_.resize(t + 1, std::nullopt);
    }
}

void IncrementalEGraph::ensureTermRegistered(EufTermId t,
                                             std::deque<PendingMerge>& outQueue) {
    // Iterative post-order over the argument DAG (was recursive on args, which
    // overflowed the stack on deeply-nested UF terms — see the deep-UF test).
    // Behavior-identical to the recursion: every node is allocated on first
    // visit, and a node's signature is refreshed only after all its args
    // (left-to-right post-order), with no early-out on already-registered terms.
    // So the congruence merges pushed to outQueue come out in the same order.
    struct Frame { EufTermId t; size_t childIdx; };
    std::vector<Frame> stack;
    ensureNodeAllocated(t);
    stack.push_back({t, 0});
    while (!stack.empty()) {
        Frame& f = stack.back();
        const auto& n = tm_.node(f.t);
        if (f.childIdx < n.args.size()) {
            EufTermId arg = n.args[f.childIdx];
            f.childIdx++;
            ensureNodeAllocated(arg);
            stack.push_back({arg, 0});   // f invalidated below this point
            continue;
        }
        EufTermId cur = f.t;
        bool hasArgs = !n.args.empty();
        stack.pop_back();
        if (hasArgs) refreshSignature(cur, outQueue);
    }
}

void IncrementalEGraph::registerPendingSignatures(std::deque<PendingMerge>& outQueue) {
    for (EufTermId t = nextTermToRegister_; t < tm_.termCount(); ++t) {
        if (!tm_.node(t).args.empty()) {
            refreshSignature(t, outQueue);
        }
    }
    nextTermToRegister_ = static_cast<EufTermId>(tm_.termCount());
}

AppSignature IncrementalEGraph::computeSignature(EufTermId t) const {
    const auto& n = tm_.node(t);
    AppSignature sig;
    sig.symbol = n.symbol;
    sig.argReps.reserve(n.args.size());
    for (EufTermId arg : n.args) {
        sig.argReps.push_back(rep(arg));
    }
    return sig;
}

std::vector<EufTermId> IncrementalEGraph::collectParents(EClassId root) const {
    std::vector<EufTermId> out;
    EClassId r = uf_.find(root);
    if (r < members_.size()) {
        for (EufTermId t : members_[r]) {
            const auto& ps = tm_.parentsOf(t);
            out.insert(out.end(), ps.begin(), ps.end());
        }
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}

void IncrementalEGraph::refreshSignature(EufTermId app,
                                         std::deque<PendingMerge>& outQueue) {
    if (app >= tm_.termCount()) return;
    if (tm_.node(app).args.empty()) return;

    // Use ensureNodeAllocated (NOT ensureTermRegistered) to avoid recursion
    for (EufTermId arg : tm_.node(app).args) {
        ensureNodeAllocated(arg);
    }
    ensureNodeAllocated(app);

    AppSignature newSig = computeSignature(app);

    std::optional<AppSignature> oldSig = currentSig_[app];

    // Step 1: Remove stale signature from sigTable_
    if (oldSig && *oldSig != newSig) {
        sigTable_.eraseIfOwner(*oldSig, app);
    }

    // Step 2: Update currentSig_ (even if congruence will be enqueued)
    if (!oldSig || *oldSig != newSig) {
        setCurrentSig(app, newSig);
    }

    // Step 3: Check for congruence with existing valid owner
    auto ownerOpt = sigTable_.find(newSig);
    if (ownerOpt) {
        EufTermId owner = *ownerOpt;

        bool ownerValid =
            owner < currentSig_.size() &&
            currentSig_[owner].has_value() &&
            *currentSig_[owner] == newSig;

        if (ownerValid) {
            if (!same(owner, app)) {
                const auto& n1 = tm_.node(owner);
                const auto& n2 = tm_.node(app);

                // Defensive: verify same symbol and arity
                assert(n1.symbol == n2.symbol);
                assert(n1.args.size() == n2.args.size());

                MergeReason cr;
                cr.kind = MergeReasonKind::Congruence;
                cr.lhsApp = owner;
                for (size_t i = 0; i < n1.args.size(); ++i) {
                    cr.argPairs.push_back({n1.args[i], n2.args[i]});
                }
                outQueue.push_back({owner, app, cr});
            }
            // Valid owner exists: do NOT replace it.  This keeps the
            // signature table stable and avoids unnecessary trail entries.
            return;
        }
    }

    // Step 4: No valid owner — app becomes owner
    sigTable_.insertOrAssign(newSig, app);
}

void IncrementalEGraph::refreshCongruence(EClassId kept, EClassId killed,
                                          std::deque<PendingMerge>& outQueue) {
    std::vector<EufTermId> affected = collectParents(kept);
    auto affectedB = collectParents(killed);
    affected.insert(affected.end(), affectedB.begin(), affectedB.end());

    for (EufTermId app : affected) {
        refreshSignature(app, outQueue);
    }
}

void IncrementalEGraph::setCurrentSig(EufTermId app, std::optional<AppSignature> sig) {
    if (currentSig_[app] == sig) return;
    currentSigTrail_.push_back({app, currentSig_[app]});
    currentSig_[app] = std::move(sig);
}

void IncrementalEGraph::rollbackCurrentSig(size_t snap) {
    while (currentSigTrail_.size() > snap) {
        auto ch = currentSigTrail_.back();
        currentSigTrail_.pop_back();
        currentSig_[ch.first] = std::move(ch.second);
    }
}

MergeResult IncrementalEGraph::merge(EufTermId a, EufTermId b,
                                       const MergeReason& reason,
                                       int level,
                                       std::deque<PendingMerge>& outQueue) {
    // Register any newly interned terms' signatures
    for (EufTermId t = nextTermToRegister_; t < tm_.termCount(); ++t) {
        if (!tm_.node(t).args.empty()) {
            refreshSignature(t, outQueue);
        }
    }
    nextTermToRegister_ = static_cast<EufTermId>(tm_.termCount());

    ensureNodeAllocated(a);
    ensureNodeAllocated(b);

    if (same(a, b)) return {false, NullEClass, NullEClass};

    EClassId ra = rep(a);
    EClassId rb = rep(b);

    if (tm_.node(a).sort != tm_.node(b).sort &&
        tm_.node(a).sort != NullSort && tm_.node(b).sort != NullSort) {
        MergeRecord rec;
        rec.id = static_cast<MergeId>(mergeRecords_.size());
        rec.lhs = a;
        rec.rhs = b;
        rec.lhsRootBefore = ra;
        rec.rhsRootBefore = rb;
        rec.merged = false;
        rec.reason = reason;
        rec.level = level;
        mergeRecords_.push_back(rec);
        return {false, NullEClass, NullEClass};
    }

    // CRITICAL: in the default path, collect affected parents BEFORE union,
    // while both roots are still valid representatives. In fast-CC mode we
    // instead collect only the LOSER class's parents AFTER union (below), since
    // only those members' representative changes.
    std::vector<EufTermId> affected;
    if (!fastMerge_) {
        affected = collectParents(ra);
        auto affectedB = collectParents(rb);
        affected.insert(affected.end(), affectedB.begin(), affectedB.end());
        std::sort(affected.begin(), affected.end());
        affected.erase(std::unique(affected.begin(), affected.end()), affected.end());
    }

    MergeRecord rec;
    rec.id = static_cast<MergeId>(mergeRecords_.size());
    rec.lhs = a;
    rec.rhs = b;
    rec.lhsRootBefore = ra;
    rec.rhsRootBefore = rb;
    rec.reason = reason;
    rec.level = level;

    auto ur = uf_.unite(ra, rb);
    if (!ur.merged) {
        rec.merged = false;
        mergeRecords_.push_back(rec);
        return {false, NullEClass, NullEClass};
    }

    EClassId dst = ur.winner;
    EClassId src = ur.loser;
    rec.kept = dst;
    rec.killed = src;
    rec.merged = true;
    mergeRecords_.push_back(rec);

    proofForest_.addEdgeAtLevel(a, b, reason, level);

    // Fast-CC: collect the LOSER class's parents now (before the member append
    // below — members_[src] still holds exactly the loser's pre-merge members,
    // whose representative just changed to dst). Only these parents can acquire
    // a new canonical signature; the winner's parents are unchanged.
    if (fastMerge_) {
        for (EufTermId m : members_[src]) {
            const auto& ps = tm_.parentsOf(m);
            affected.insert(affected.end(), ps.begin(), ps.end());
        }
        std::sort(affected.begin(), affected.end());
        affected.erase(std::unique(affected.begin(), affected.end()), affected.end());
    }

    memberTrail_.push_back({dst, src, members_[dst].size()});
    members_[dst].insert(members_[dst].end(),
                         members_[src].begin(), members_[src].end());

    // Refresh signatures for all affected parents.  Congruences are
    // pushed to outQueue and will be processed by the saturation loop.
    for (EufTermId app : affected) {
        refreshSignature(app, outQueue);
    }

    return {true, dst, src};
}

bool IncrementalEGraph::same(EufTermId a, EufTermId b) const {
    return uf_.same(a, b);
}

EClassId IncrementalEGraph::rep(EufTermId t) const {
    if (t >= members_.size()) return NullEClass;
    return uf_.find(t);
}

EGraphSnapshot IncrementalEGraph::snapshot() const {
#ifndef NDEBUG
    static int snapCount = 0;
    ++snapCount;
    FILE* dbg = fopen("/tmp/sig_inv_fail.log", "a");
    if (dbg) { fprintf(dbg, "[SNAPSHOT] #%d terms=%zu\n", snapCount, tm_.termCount()); fclose(dbg); }
    checkSignatureTableInvariant();
#endif
    return {
        uf_.snapshot(),
        memberTrail_.size(),
        mergeRecords_.size(),
        sigTable_.snapshot(),
        currentSigTrail_.size(),
        proofForest_.snapshot(),
        nextTermToRegister_
    };
}

void IncrementalEGraph::rollback(EGraphSnapshot snap) {
#ifndef NDEBUG
    FILE* dbg = fopen("/tmp/sig_inv_fail.log", "a");
    if (dbg) {
        fprintf(dbg, "[EGRAPH_ROLLBACK] sigSnap=%zu csSnap=%zu pfSnap=%zu ufSnap=%zu\n",
                snap.sigTableSnap, snap.currentSigSnap, snap.proofForestSnap, snap.ufTrailSize);
        fprintf(dbg, "  before csTrail=%zu sigTrail=%zu\n", currentSigTrail_.size(), sigTable_.snapshot());
        fclose(dbg);
    }
#endif
    proofForest_.rollback(snap.proofForestSnap);
    mergeRecords_.resize(snap.mergeRecordSize);
    nextTermToRegister_ = snap.nextTermToRegister;
    rollbackCurrentSig(snap.currentSigSnap);
    sigTable_.rollback(snap.sigTableSnap);
#ifndef NDEBUG
    dbg = fopen("/tmp/sig_inv_fail.log", "a");
    if (dbg) {
        fprintf(dbg, "  after csTrail=%zu sigTrail=%zu\n", currentSigTrail_.size(), sigTable_.snapshot());
        fclose(dbg);
    }

    // Verify rollback actually truncated the trail
    if (sigTable_.snapshot() != snap.sigTableSnap) {
        FILE* dbg2 = fopen("/tmp/sig_inv_fail.log", "a");
        if (dbg2) {
            fprintf(dbg2, "[ROLLBACK_BUG] sigTable trail after rollback=%zu expected=%zu\n",
                    sigTable_.snapshot(), snap.sigTableSnap);
            fclose(dbg2);
        }
    }
#endif

    while (memberTrail_.size() > snap.memberTrailSize) {
        auto ch = memberTrail_.back();
        memberTrail_.pop_back();
        members_[ch.dstRoot].resize(ch.oldDstSize);
    }

    uf_.rollback(snap.ufTrailSize);

#ifndef NDEBUG
    checkSignatureTableInvariant();
#endif
}

bool IncrementalEGraph::hasTrueFalseConflict() const {
    if (trueTerm_ == NullEufTerm || falseTerm_ == NullEufTerm) return false;
    return same(trueTerm_, falseTerm_);
}

uint64_t IncrementalEGraph::canonicalPairKey(EufTermId a, EufTermId b) {
    if (a > b) std::swap(a, b);
    return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
}

ExplainResult IncrementalEGraph::explainEquality(EufTermId a, EufTermId b) {
    // Iterative DFS over the proof forest. The former explainEquality<->explainEdge
    // mutual recursion (depth = UF nesting) overflowed the stack on deeply-nested
    // UF. This is BEHAVIOR-IDENTICAL: same success-only memoization, same on-stack
    // cycle guard (activePairs), same per-call order-preserving dedup of reasons,
    // and same failure propagation — so the explanation literal SET (and order) is
    // unchanged. That equivalence is load-bearing: this is the UNSAT/conflict
    // explanation path, where a different reason set would be a false-UNSAT.
    //
    // Frame model: an Eq frame explains a pair (a,b) by walking its proof-forest
    // edge path and folding each edge's explanation; an Edge frame explains one
    // edge — an AssertedEquality contributes its literal directly, a congruence
    // edge folds the explanation of each arg pair. A frame pushes a child frame
    // and suspends; when the child pops, its result is in `ret` and the parent
    // (now on top, already initialized) folds it in and advances.
    std::unordered_map<uint64_t, ExplainResult> memo;
    std::unordered_set<uint64_t> activePairs;

    struct Frame {
        bool isEdge = false;
        bool initialized = false;
        // Eq frame
        EufTermId a = NullEufTerm, b = NullEufTerm;
        uint64_t key = 0;
        bool keyInserted = false;
        std::vector<size_t> edgeIds;
        // Edge frame
        size_t edgeId = 0;
        // common
        size_t i = 0;
        std::vector<SatLit> acc;
    };

    auto dedupAppend = [](std::vector<SatLit>& dst, const std::vector<SatLit>& src) {
        for (SatLit lit : src) {
            bool found = false;
            for (SatLit r : dst) {
                if (r.var == lit.var && r.sign == lit.sign) { found = true; break; }
            }
            if (!found) dst.push_back(lit);
        }
    };

    std::vector<Frame> stack;
    {
        Frame root;
        root.isEdge = false;
        root.a = a;
        root.b = b;
        stack.push_back(std::move(root));
    }

    ExplainResult ret{false, {}};

    while (!stack.empty()) {
        Frame& f = stack.back();

        if (!f.initialized) {
            f.initialized = true;
            if (!f.isEdge) {
                // ENTER explainEquality(f.a, f.b) — checks in the recursion's order.
                if (f.a == f.b) { ret = {true, {}}; stack.pop_back(); continue; }
                if (!same(f.a, f.b)) { ret = {false, {}}; stack.pop_back(); continue; }
                f.key = canonicalPairKey(f.a, f.b);
                if (auto it = memo.find(f.key); it != memo.end()) {
                    ret = it->second; stack.pop_back(); continue;
                }
                if (!activePairs.insert(f.key).second) {
                    // Cycle: pair already on the active path. Fail WITHOUT erasing
                    // (the owning ancestor frame erases it when it unwinds).
                    ret = {false, {}}; stack.pop_back(); continue;
                }
                f.keyInserted = true;
                f.edgeIds = proofForest_.path(f.a, f.b);
                if (f.edgeIds.empty()) {
                    activePairs.erase(f.key);
                    ret = {false, {}}; stack.pop_back(); continue;
                }
                f.i = 0;
                // fall through to child dispatch
            } else {
                // ENTER explainEdge(f.edgeId)
                const auto& edge = proofForest_.edgeReason(f.edgeId);
                if (edge.kind == MergeReasonKind::AssertedEquality) {
                    ret = {true, {edge.lit}}; stack.pop_back(); continue;
                }
                f.i = 0;
                // fall through to child dispatch
            }
        } else {
            // RESUME: a child frame completed; its result is in `ret`.
            if (!ret.ok) {
                if (!f.isEdge && f.keyInserted) activePairs.erase(f.key);
                ret = {false, {}};
                stack.pop_back();
                continue;
            }
            dedupAppend(f.acc, ret.reasons);
            f.i++;
        }

        // CHILD DISPATCH: push the next child, or complete this frame.
        if (!f.isEdge) {
            if (f.i < f.edgeIds.size()) {
                size_t eid = f.edgeIds[f.i];
                Frame child;
                child.isEdge = true;
                child.edgeId = eid;
                stack.push_back(std::move(child));   // f invalidated below
                continue;
            }
            uint64_t key = f.key;
            bool keyInserted = f.keyInserted;
            ExplainResult res{true, std::move(f.acc)};
            if (keyInserted) activePairs.erase(key);
            memo[key] = res;
            ret = std::move(res);
            stack.pop_back();
            continue;
        } else {
            const auto& argPairs = proofForest_.edgeReason(f.edgeId).argPairs;
            while (f.i < argPairs.size() && argPairs[f.i].first == argPairs[f.i].second) {
                f.i++;
            }
            if (f.i < argPairs.size()) {
                EufTermId ai = argPairs[f.i].first;
                EufTermId bi = argPairs[f.i].second;
                Frame child;
                child.isEdge = false;
                child.a = ai;
                child.b = bi;
                stack.push_back(std::move(child));   // f invalidated below
                continue;
            }
            ret = {true, std::move(f.acc)};
            stack.pop_back();
            continue;
        }
    }

    return ret;
}

#ifndef NDEBUG
void IncrementalEGraph::checkSignatureTableInvariant() const {
    for (const auto& [sig, owner] : sigTable_.internalTable()) {
        assert(currentSig_[owner].has_value());
        assert(*currentSig_[owner] == sig);
        auto computed = computeSignature(owner);
        assert(computed == sig);
    }
    for (EufTermId t = 0; t < currentSig_.size(); ++t) {
        if (currentSig_[t]) {
            auto it = sigTable_.find(*currentSig_[t]);
            if (!it.has_value()) {
                FILE* dbg = fopen("/tmp/sig_inv_fail.log", "a");
                if (dbg) { fprintf(dbg, "[SIG_INV_FAIL] t=%u sig not in table\n", t); fclose(dbg); }
                assert(false);
            }
            if (*it != t && !same(*it, t)) {
                FILE* dbg = fopen("/tmp/sig_inv_fail.log", "a");
                if (dbg) {
                    fprintf(dbg, "[SIG_INV_FAIL] t=%u owner=%u same=%d\n", t, *it, same(*it, t));
                    const auto& nt = tm_.node(t);
                    const auto& no = tm_.node(*it);
                    fprintf(dbg, "  t symbol=%u sort=%u arity=%zu\n", nt.symbol, nt.sort, nt.args.size());
                    fprintf(dbg, "  owner symbol=%u sort=%u arity=%zu\n", no.symbol, no.sort, no.args.size());
                    for (size_t i = 0; i < nt.args.size(); ++i) {
                        fprintf(dbg, "  t.arg[%zu]=%u rep=%u\n", i, nt.args[i], rep(nt.args[i]));
                    }
                    for (size_t i = 0; i < no.args.size(); ++i) {
                        fprintf(dbg, "  owner.arg[%zu]=%u rep=%u\n", i, no.args[i], rep(no.args[i]));
                    }
                    fprintf(dbg, "  ufTrailSize=%zu sigTableTrail=%zu currentSigTrail=%zu\n",
                            uf_.snapshot(), sigTable_.internalTable().size(), currentSigTrail_.size());
                    fprintf(dbg, "  find(t)=%u find(owner)=%u parentSize=%zu\n",
                            uf_.find(t), uf_.find(*it), uf_.size());
                    fclose(dbg);
                }
                assert(false);
            }
        }
    }
}

bool IncrementalEGraph::congruenceClosed() const {
    // All interned terms must have been registered by registerPendingSignatures
    if (nextTermToRegister_ != tm_.termCount()) {
        return false;
    }

    std::unordered_map<AppSignature, EufTermId, AppSignatureHash> seen;

    for (EufTermId t = 0; t < tm_.termCount(); ++t) {
        const auto& node = tm_.node(t);
        if (node.args.empty()) continue;

        // Every app term MUST have a registered signature.
        // DO NOT skip missing signatures — that would hide the core bug.
        if (t >= currentSig_.size()) return false;
        if (!currentSig_[t].has_value()) return false;

        // Signature must match recomputed canonical signature
        AppSignature actual = computeSignature(t);
        if (*currentSig_[t] != actual) return false;

        // All terms with same canonical signature must be same-class
        auto it = seen.find(actual);
        if (it == seen.end()) {
            seen.emplace(actual, t);
        } else {
            if (!same(it->second, t)) {
                return false;
            }
        }
    }
    return true;
}
#endif

} // namespace xolver
