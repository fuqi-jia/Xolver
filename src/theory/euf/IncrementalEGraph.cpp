#include "theory/euf/IncrementalEGraph.h"
#include <cassert>
#include <algorithm>
#include <queue>
#include <iostream>

namespace nlcolver {

struct ExplainContext {
    std::unordered_map<uint64_t, ExplainResult> memo;
    std::unordered_set<uint64_t> activePairs;
};

IncrementalEGraph::IncrementalEGraph(EufTermManager& tm) : tm_(tm) {}

void IncrementalEGraph::clear() {
    uf_ = RollbackUnionFind();
    members_.clear();
    memberTrail_.clear();
    mergeRecords_.clear();
    mergeQueue_.clear();
    sigTable_.clear();
    currentSig_.clear();
    currentSigTrail_.clear();
    proofForest_.clear();
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;
    nextTermToRegister_ = 0;
}

void IncrementalEGraph::ensureTerm(EufTermId t) {
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

void IncrementalEGraph::refreshSignature(EufTermId app) {
    if (app >= tm_.termCount()) return;
    if (tm_.node(app).args.empty()) return;

    for (EufTermId arg : tm_.node(app).args) {
        ensureTerm(arg);
    }
    ensureTerm(app);

    AppSignature newSig = computeSignature(app);

    auto ownerOpt = sigTable_.find(newSig);
    if (ownerOpt) {
        EufTermId owner = *ownerOpt;
        bool ownerIsFresh = currentSig_[owner].has_value() &&
                            *currentSig_[owner] == newSig;
        // std::cerr << " owner=" << owner
        //           << " fresh=" << ownerIsFresh
        //           << " same=" << same(owner, app) << "\n";
        if (ownerIsFresh && !same(owner, app)) {
            MergeReason cr;
            cr.kind = MergeReasonKind::Congruence;
            cr.lhsApp = owner;
            cr.rhsApp = app;
            const auto& n1 = tm_.node(owner);
            const auto& n2 = tm_.node(app);
            for (size_t i = 0; i < n1.args.size(); ++i) {
                cr.argPairs.push_back({n1.args[i], n2.args[i]});
            }
            mergeQueue_.push_back({owner, app, cr});
            return;
        }
    }

    if (currentSig_[app].has_value()) {
        sigTable_.eraseIfOwner(*currentSig_[app], app);
    }

    sigTable_.insertOrAssign(newSig, app);
    setCurrentSig(app, newSig);
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

MergeStatus IncrementalEGraph::processMergeQueue() {
    // std::cerr << " count=" << tm_.termCount() << "\n";
    for (EufTermId t = nextTermToRegister_; t < tm_.termCount(); ++t) {
        if (!tm_.node(t).args.empty()) {
            refreshSignature(t);
        }
    }
    nextTermToRegister_ = static_cast<EufTermId>(tm_.termCount());

    while (!mergeQueue_.empty()) {
        auto m = mergeQueue_.front();
        mergeQueue_.pop_front();

        if (same(m.a, m.b)) continue;

        EClassId ra = rep(m.a);
        EClassId rb = rep(m.b);

        if (tm_.node(m.a).sort != tm_.node(m.b).sort &&
            tm_.node(m.a).sort != NullSort && tm_.node(m.b).sort != NullSort) {
            return MergeStatus::SortMismatch;
        }

        std::vector<EufTermId> affected = collectParents(ra);
        auto affectedB = collectParents(rb);
        affected.insert(affected.end(), affectedB.begin(), affectedB.end());

        MergeRecord rec;
        rec.id = static_cast<MergeId>(mergeRecords_.size());
        rec.lhs = m.a;
        rec.rhs = m.b;
        rec.lhsRootBefore = ra;
        rec.rhsRootBefore = rb;
        rec.reason = m.reason;
        mergeRecords_.push_back(rec);

        auto ur = uf_.unite(ra, rb);
        if (!ur.merged) continue;
        EClassId dst = ur.winner;
        EClassId src = ur.loser;

        proofForest_.addEdge(m.a, m.b, m.reason);

        memberTrail_.push_back({dst, src, members_[dst].size()});
        members_[dst].insert(members_[dst].end(), members_[src].begin(), members_[src].end());

        for (EufTermId app : affected) {
            refreshSignature(app);
        }
    }
#ifndef NDEBUG
    checkSignatureTableInvariant();
#endif
    return MergeStatus::Ok;
}

MergeStatus IncrementalEGraph::merge(EufTermId a, EufTermId b, const MergeReason& reason) {
    mergeQueue_.push_back({a, b, reason});
    return processMergeQueue();
}

bool IncrementalEGraph::same(EufTermId a, EufTermId b) const {
    return uf_.same(a, b);
}

EClassId IncrementalEGraph::rep(EufTermId t) const {
    if (t >= members_.size()) return NullEClass;
    return uf_.find(t);
}

EGraphSnapshot IncrementalEGraph::snapshot() const {
    assert(mergeQueue_.empty());
    return {
        uf_.snapshot(),
        memberTrail_.size(),
        mergeRecords_.size(),
        mergeQueue_.size(),
        sigTable_.snapshot(),
        currentSigTrail_.size(),
        proofForest_.snapshot(),
        nextTermToRegister_
    };
}

void IncrementalEGraph::rollback(EGraphSnapshot snap) {
    mergeQueue_.resize(snap.mergeQueueSize);

    proofForest_.rollback(snap.proofForestSnap);
    mergeRecords_.resize(snap.mergeRecordSize);

    nextTermToRegister_ = snap.nextTermToRegister;
    rollbackCurrentSig(snap.currentSigSnap);
    sigTable_.rollback(snap.sigTableSnap);

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
    ExplainContext ctx;
    return explainEquality(a, b, ctx);
}

ExplainResult IncrementalEGraph::explainEquality(EufTermId a, EufTermId b, ExplainContext& ctx) {
    if (a == b) return {true, {}};
    if (!same(a, b)) return {false, {}};

    uint64_t key = canonicalPairKey(a, b);
    if (auto it = ctx.memo.find(key); it != ctx.memo.end()) {
        return it->second;
    }
    if (!ctx.activePairs.insert(key).second) {
        return {false, {}};
    }

    auto edgeIds = proofForest_.path(a, b);
    if (edgeIds.empty()) {
        ctx.activePairs.erase(key);
        return {false, {}};
    }

    std::vector<SatLit> reasons;
    for (size_t eid : edgeIds) {
        auto sub = explainEdge(eid, ctx);
        if (!sub.ok) {
            ctx.activePairs.erase(key);
            return {false, {}};
        }
        for (SatLit lit : sub.reasons) {
            bool found = false;
            for (SatLit r : reasons) {
                if (r.var == lit.var && r.sign == lit.sign) {
                    found = true;
                    break;
                }
            }
            if (!found) reasons.push_back(lit);
        }
    }

    ctx.activePairs.erase(key);
    ExplainResult result{true, std::move(reasons)};
    ctx.memo[key] = result;
    return result;
}

ExplainResult IncrementalEGraph::explainEdge(size_t edgeId, ExplainContext& ctx) {
    const auto& edge = proofForest_.edgeReason(edgeId);

    if (edge.kind == MergeReasonKind::AssertedEquality) {
        return {true, {edge.assertedLit}};
    }

    std::vector<SatLit> out;
    for (const auto& [ai, bi] : edge.argPairs) {
        if (ai == bi) continue;
        auto sub = explainEquality(ai, bi, ctx);
        if (!sub.ok) {
            return {false, {}};
        }
        for (SatLit lit : sub.reasons) {
            bool found = false;
            for (SatLit existing : out) {
                if (existing.var == lit.var && existing.sign == lit.sign) {
                    found = true;
                    break;
                }
            }
            if (!found) out.push_back(lit);
        }
    }
    return {true, std::move(out)};
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
            assert(it.has_value());
            assert(*it == t || same(*it, t));
        }
    }
}
#endif

} // namespace nlcolver
