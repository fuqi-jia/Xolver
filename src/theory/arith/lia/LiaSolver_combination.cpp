#include "util/MpqUtils.h"
#include "theory/arith/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/arith/lia/GomoryCut.h"
#include "theory/arith/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include "theory/arith/nia/reasoners/DioReasoner.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

// NOTE: This translation unit was split out of LiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

int LiaSolver::getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = interfaceEqAuxVars_.find(key);
    if (it != interfaceEqAuxVars_.end()) return it->second;

    std::string va = getVarNameForSharedTerm(a);
    std::string vb = getVarNameForSharedTerm(b);

    bool aIsConst = false, bIsConst = false;
    mpq_class aVal, bVal;
    if (sharedTermRegistry_ && coreIr_) {
        if (const auto* stA = sharedTermRegistry_->get(a)) {
            const auto& exprA = coreIr_->get(stA->coreExpr);
            if (exprA.isConst()) {
                aIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprA.payload.value)) aVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprA.payload.value)) aVal = mpqFromString(*s);
            }
        }
        if (const auto* stB = sharedTermRegistry_->get(b)) {
            const auto& exprB = coreIr_->get(stB->coreExpr);
            if (exprB.isConst()) {
                bIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprB.payload.value)) bVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprB.payload.value)) bVal = mpqFromString(*s);
            }
        }
    }

    int aux = -1;
    if (aIsConst && bIsConst) {
        if (aVal == bVal) return -1;
        return -1;
    } else if (aIsConst) {
        if (vb.empty()) return -1;
        int vB = manager_.getOrCreateVar(gs_, vb);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vB, mpq_class(1)});
        aux = gs_.addConstraint(terms, aVal);
    } else if (bIsConst) {
        if (va.empty()) return -1;
        int vA = manager_.getOrCreateVar(gs_, va);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vA, mpq_class(1)});
        aux = gs_.addConstraint(terms, bVal);
    } else {
        if (va.empty() || vb.empty()) return -1;
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
        aux = gs_.addConstraint(terms, mpq_class(0));
    }

    interfaceEqAuxVars_[key] = aux;
    return aux;
}

std::vector<SatLit>
LiaSolver::assertedVarEqualityReason(SharedTermId a, SharedTermId b) const {
    if (!sharedTermRegistry_) return {};
    // Names of the two (non-const) shared variables.
    auto nameOf = [&](SharedTermId s) -> std::string {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) return "";
            auto it = sharedTermToVarName_.find(s);
            if (it != sharedTermToVarName_.end()) return it->second;
            const auto& e = coreIr_->get(st->coreExpr);
            if (e.kind == Kind::Variable &&
                std::holds_alternative<std::string>(e.payload.value)) {
                return std::get<std::string>(e.payload.value);
            }
        }
        return "";
    };
    std::string na = nameOf(a), nb = nameOf(b);
    if (na.empty() || nb.empty() || na == nb) return {};

    // Aggregate the asserted linear (in)equality atoms whose canonical LHS is a
    // 2-variable difference form {(na,c),(nb,-c)} into a single interval on the
    // normalized difference d = (na - nb). Each atom contributes a lower and/or
    // upper bound on d (after dividing by c and flipping for negative c). If the
    // accumulated interval pins d == 0, then na = nb is entailed and we return
    // the reason literals of the atoms that did the pinning. This covers BOTH
    // an explicit equality atom (na - nb = 0; both bounds 0 — repro R4) and two
    // complementary inequalities (na <= nb and nb <= na ⟹ na = nb — repro e6).
    bool haveLo = false, haveUp = false;
    mpq_class lo = 0, up = 0;
    SatLit loLit{}, upLit{};
    for (const auto& e : theoryTrail_) {
        if (e.isDiseq) continue;
        if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
        if (payload.lhs.terms.size() != 2) continue;
        const auto& t0 = payload.lhs.terms[0];
        const auto& t1 = payload.lhs.terms[1];
        if (t0.second == 0 || t0.second != -t1.second) continue;  // form c*x - c*y
        // Orient so that the form reads (na - nb) * c0.
        mpq_class c0;
        if (t0.first == na && t1.first == nb)      c0 = t0.second;   // (na - nb)*c0
        else if (t0.first == nb && t1.first == na) c0 = t1.second;   // (na - nb)*c0
        else continue;
        // payload: (form) rel rhs, asserted with polarity e.value. Effective
        // relation on the form value F = c0*(na-nb):
        Relation rel = e.value ? payload.rel : negateRelation(payload.rel);
        const mpq_class& rhs = payload.rhs.asRational();
        // Reduce to bounds on d = na - nb: F = c0*d, F rel rhs  ⟹  d rel' rhs/c0.
        mpq_class bnd = rhs / c0;
        bool flip = (c0 < 0);
        auto addLower = [&](const mpq_class& v, SatLit lit) {
            if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
        };
        auto addUpper = [&](const mpq_class& v, SatLit lit) {
            if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
        };
        switch (rel) {
            case Relation::Eq:
                addLower(bnd, e.lit); addUpper(bnd, e.lit); break;
            case Relation::Leq:
                if (!flip) addUpper(bnd, e.lit); else addLower(bnd, e.lit); break;
            case Relation::Geq:
                if (!flip) addLower(bnd, e.lit); else addUpper(bnd, e.lit); break;
            case Relation::Lt:    // integers: d < bnd  ⟺  d <= bnd-1 (only used to pin via combo; treat conservatively as <= for difference-equality detection only when integral)
            case Relation::Gt:
            default:
                break;  // strict bounds don't pin an equality; skip
        }
    }
    if (haveLo && haveUp && lo == 0 && up == 0) {
        std::vector<SatLit> reasons;
        reasons.push_back(loLit);
        if (!(upLit == loLit)) reasons.push_back(upLit);
        return reasons;
    }
    return {};
}

TheoryCheckResult LiaSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    // Remove stale disequality for the same pair
    auto it = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [a, b](const auto& d) { return d.a == a && d.b == b; });
    interfaceDisequalities_.erase(it, interfaceDisequalities_.end());

    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    // Remove stale equality for the same pair
    auto it = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [a, b](const auto& e) { return e.a == a && e.b == b; });
    const bool removedEq = (it != interfaceEqualities_.end());
    interfaceEqualities_.erase(it, interfaceEqualities_.end());

    interfaceDisequalities_.push_back({a, b, reason, level});
    // Invalidate simplex state ONLY when this disequality actually removed a
    // previously-applied interface EQUALITY bound — that is the only way a pending
    // diseq perturbs the simplex (a!=b itself is recorded for conflict detection,
    // not applied as a bound). The unconditional full rebuild re-applied every
    // bound on each diseq; the Nelson-Oppen arrangement asserts MANY value-distinct
    // diseqs with no prior equality (the SAT solver decides a!=b directly), so the
    // reset was almost always wasted — assertInterfaceDisequality + the GeneralSimplex
    // rebuild dominated the QF_UFLIA Wisa profile. Verdict-identical: with no equality
    // bound removed, no simplex bound changed, so the reset would be a no-op.
    if (removedEq) {
        gs_.resetActiveBounds();
        appliedCursor_ = 0;
    }
    return TheoryCheckResult::consistent();
}

// Track A mirror for LIA (see LraSolver::tryProvePairEqualityByLpDuality for
// the discipline). Same RAII, marker filter, conflict-state clear.
bool LiaSolver::tryProvePairEqualityByLpDuality(int aux, std::vector<SatLit>& outReasons) {
    static const SatLit MARKER{0, true};
    struct ProbeScope {
        GeneralSimplex& gs;
        int level;
        ProbeScope(GeneralSimplex& g, int lvl) : gs(g), level(lvl) { gs.push(); }
        ~ProbeScope() { gs.pop(); gs.backtrackToLevel(level); }
        ProbeScope(const ProbeScope&) = delete;
        ProbeScope& operator=(const ProbeScope&) = delete;
    };
    auto collectAndFilter = [&](std::vector<SatLit>& out) {
        for (const auto& br : gs_.getConflict()) {
            if (br.reason == MARKER) continue;
            out.push_back(br.reason);
        }
    };
    std::vector<SatLit> upperReasons, lowerReasons;
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(-1))), MARKER);
        bool ok = gs_.assertUpper(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(upperReasons);
        if (!unsat) return false;
    }
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(1))), MARKER);
        bool ok = gs_.assertLower(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(lowerReasons);
        if (!unsat) return false;
    }
    outReasons = std::move(upperReasons);
    outReasons.insert(outReasons.end(), lowerReasons.begin(), lowerReasons.end());
    std::sort(outReasons.begin(), outReasons.end(),
        [](SatLit a, SatLit b) {
            if (a.var != b.var) return a.var < b.var;
            return a.sign < b.sign;
        });
    outReasons.erase(std::unique(outReasons.begin(), outReasons.end(),
        [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), outReasons.end());
    assert(std::none_of(outReasons.begin(), outReasons.end(),
        [](const SatLit& r) { return r == MARKER; }) &&
        "Track A LIA: marker bound leaked into emitted reason set");
    return true;
}

std::vector<TheorySolver::SharedEqualityPropagation>
LiaSolver::getDeducedSharedEqualities() {
    if (!sharedTermRegistry_) return {};

    // Build name -> simplex var map
    std::unordered_map<std::string, int> nameToVar;
    for (int i = 0; i < gs_.numVars(); ++i) {
        nameToVar[gs_.varName(i)] = i;
    }

    // Map fixed-value shared terms
    using GroupEntry = std::pair<SharedTermId, std::vector<SatLit>>;
    std::map<DeltaRational, std::vector<GroupEntry>> groups;

    for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
        std::string name = getVarNameForSharedTerm(stId);
        if (name.empty()) continue;
        auto it = nameToVar.find(name);
        if (it == nameToVar.end()) continue;
        int var = it->second;

        auto fixedOpt = gs_.proveFixedValue(var);
        if (!fixedOpt) continue;

        const DeltaRational& val = fixedOpt->first;
        std::vector<SatLit> reasons;
        for (const auto& br : fixedOpt->second) {
            reasons.push_back(br.reason);
        }
        std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), reasons.end());
        groups[val].push_back({stId, std::move(reasons)});
    }

    std::vector<TheorySolver::SharedEqualityPropagation> result;
    for (auto& [valKey, terms] : groups) {
        if (terms.size() < 2) continue;
        for (size_t i = 0; i < terms.size(); ++i) {
            for (size_t j = i + 1; j < terms.size(); ++j) {
                std::vector<SatLit> reasons;
                reasons.insert(reasons.end(), terms[i].second.begin(), terms[i].second.end());
                reasons.insert(reasons.end(), terms[j].second.begin(), terms[j].second.end());
                std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
                    return a.var < b.var || (a.var == b.var && a.sign < b.sign);
                });
                reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
                    return a.var == b.var && a.sign == b.sign;
                }), reasons.end());
                result.push_back(TheorySolver::SharedEqualityPropagation{terms[i].first, terms[j].first, std::move(reasons)});
            }
        }
    }

    // Variable-variable implied equalities. The fixed-value grouping above only
    // catches terms pinned to a constant. But asserted linear facts can make two
    // shared variables equal WITHOUT fixing either to a value: an equality atom
    // (+ i 1)=(+ j 1) normalizing to (i - j = 0) (repro R4), or two
    // complementary inequalities i<=j and j<=i pinning (i - j) to 0 (repro e6).
    // Such implied equalities must be propagated to EUF so array Row1/congruence
    // fires (select(store(a,i,v),j) with i=j collapses to v). For each pair of
    // NON-constant shared variables, assertedVarEqualityReason reports the
    // proving reason literals (or empty). Sound: only fires when the asserted
    // atoms genuinely pin the difference to 0. Bounded by #distinct shared vars.
    {
        std::vector<SharedTermId> sharedVars;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            if (const auto* st = sharedTermRegistry_->get(stId)) {
                if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;
            }
            std::string nm = getVarNameForSharedTerm(stId);
            if (nm.empty()) continue;
            if (nameToVar.find(nm) == nameToVar.end()) continue;
            sharedVars.push_back(stId);
        }
        const int n = static_cast<int>(sharedVars.size());
        std::vector<std::vector<std::pair<int, std::vector<SatLit>>>> adj(n);

        // iter-97 perf: assertedVarEqualityReason previously walked the ENTIRE
        // theoryTrail_ for every pair (i,j), giving O(N² × |trail|) total cost.
        // Pre-index the trail's 2-var linear non-diseq entries by sorted (n1,n2)
        // name pair ONCE; the inner loop then does O(log) map lookup + iterate
        // only the relevant entries. Soundness invariant unchanged: the per-pair
        // lo/up aggregation is byte-for-byte identical to the original
        // assertedVarEqualityReason; only the trail-scan ordering is changed.
        //
        // Mirrors iter-96 f41de5b LRA fix — same anti-pattern in LIA.
        struct TwoVarEntry {
            std::string n0, n1;
            mpq_class c0;
            Relation rel;
            mpq_class rhs;
            SatLit lit;
        };
        std::map<std::pair<std::string, std::string>, std::vector<TwoVarEntry>> twoVarIndex;
        for (const auto& e : theoryTrail_) {
            if (e.isDiseq) continue;
            if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
            const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
            if (payload.lhs.terms.size() != 2) continue;
            const auto& t0 = payload.lhs.terms[0];
            const auto& t1 = payload.lhs.terms[1];
            if (t0.second == 0 || t0.second != -t1.second) continue;
            Relation rel = e.value ? payload.rel : negateRelation(payload.rel);
            std::string a = t0.first, b = t1.first;
            if (a > b) {
                std::swap(a, b);
                twoVarIndex[{a, b}].push_back({a, b, t1.second, rel, payload.rhs.asRational(), e.lit});
            } else {
                twoVarIndex[{a, b}].push_back({a, b, t0.second, rel, payload.rhs.asRational(), e.lit});
            }
        }

        // Cache shared term names once (was O(N) lookups inside O(N²) loop).
        std::vector<std::string> sharedNames(n);
        for (int i = 0; i < n; ++i) {
            sharedNames[i] = getVarNameForSharedTerm(sharedVars[i]);
        }

        for (int i = 0; i < n; ++i) {
            const std::string& na = sharedNames[i];
            if (na.empty()) continue;
            for (int j = i + 1; j < n; ++j) {
                const std::string& nb = sharedNames[j];
                if (nb.empty() || na == nb) continue;
                std::string ka = na, kb = nb;
                if (ka > kb) std::swap(ka, kb);
                auto it = twoVarIndex.find({ka, kb});
                if (it == twoVarIndex.end()) continue;

                bool haveLo = false, haveUp = false;
                mpq_class lo = 0, up = 0;
                SatLit loLit{}, upLit{};
                auto addLower = [&](const mpq_class& v, SatLit lit) {
                    if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
                };
                auto addUpper = [&](const mpq_class& v, SatLit lit) {
                    if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
                };
                for (const auto& te : it->second) {
                    mpq_class c0;
                    if (te.n0 == na && te.n1 == nb) c0 = te.c0;
                    else if (te.n0 == nb && te.n1 == na) c0 = -te.c0;
                    else continue;
                    mpq_class bnd = te.rhs / c0;
                    bool flip = (c0 < 0);
                    switch (te.rel) {
                        case Relation::Eq: addLower(bnd, te.lit); addUpper(bnd, te.lit); break;
                        case Relation::Leq: if (!flip) addUpper(bnd, te.lit); else addLower(bnd, te.lit); break;
                        case Relation::Geq: if (!flip) addLower(bnd, te.lit); else addUpper(bnd, te.lit); break;
                        default: break;  // strict bounds don't pin a difference-equality
                    }
                }
                if (!(haveLo && haveUp && lo == 0 && up == 0)) continue;
                std::vector<SatLit> reasons;
                reasons.push_back(loLit);
                if (!(upLit == loLit)) reasons.push_back(upLit);

                adj[i].push_back({j, reasons});
                adj[j].push_back({i, reasons});
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    sharedVars[i], sharedVars[j], std::move(reasons)});
            }
        }

        // Track 2b Step 1 (XOLVER_SIMPLEX_IMPLIED_EQ): transitive closure over
        // the direct-pair edges. If two shared vars are linked through a chain
        // of asserted equalities (x = z and z = y), emit x = y too with the
        // UNION of all SatLits along the BFS path. Sound by construction.
        // Deduped against direct pairs emitted above.
        if (impliedEqEnabled_ && n > 2) {
            auto pairKey = [](int a, int b) -> uint64_t {
                int lo = std::min(a, b), hi = std::max(a, b);
                return (static_cast<uint64_t>(lo) << 32) | static_cast<uint32_t>(hi);
            };
            std::unordered_set<uint64_t> emittedPair;
            for (int i = 0; i < n; ++i)
                for (const auto& [j, rs] : adj[i])
                    if (i < j) emittedPair.insert(pairKey(i, j));
            for (int i = 0; i < n; ++i) {
                std::vector<int> parent(n, -1);
                std::vector<std::vector<SatLit>> edgeRs(n);
                std::vector<int> bfs;
                parent[i] = i;
                bfs.push_back(i);
                for (size_t head = 0; head < bfs.size(); ++head) {
                    int u = bfs[head];
                    for (const auto& [v, rs] : adj[u]) {
                        if (parent[v] != -1) continue;
                        parent[v] = u;
                        edgeRs[v] = rs;
                        bfs.push_back(v);
                    }
                }
                for (int j = i + 1; j < n; ++j) {
                    if (parent[j] == -1) continue;
                    if (emittedPair.count(pairKey(i, j))) continue;
                    std::vector<SatLit> chain;
                    for (int cur = j; cur != i; cur = parent[cur])
                        for (SatLit s : edgeRs[cur]) chain.push_back(s);
                    std::sort(chain.begin(), chain.end(),
                        [](SatLit a, SatLit b) {
                            if (a.var != b.var) return a.var < b.var;
                            return a.sign < b.sign;
                        });
                    chain.erase(std::unique(chain.begin(), chain.end(),
                        [](SatLit a, SatLit b) {
                            return a.var == b.var && a.sign == b.sign;
                        }), chain.end());
                    emittedPair.insert(pairKey(i, j));
                    result.push_back(TheorySolver::SharedEqualityPropagation{
                        sharedVars[i], sharedVars[j], std::move(chain)});
                }
            }
        }
    }

    // Definitional-form implied equalities (N-variable). assertedVarEqualityReason
    // only pins a 2-variable DIFFERENCE atom (na - nb = 0). But two shared vars
    // each asserted equal to the SAME linear form via SEPARATE multi-variable
    // equalities (e.g. `bridge = bz+ba` and `q = bz+ba`, two 3-var equalities)
    // are equal by transitivity through the shared form — a linear COMBINATION the
    // 2-var scan cannot see. This is the computed-array-index combination case
    // (read2): the LIA-entailed index equality must reach EUF so array Row1/Row2
    // fires. For each active equality atom and each shared var v in it, build the
    // canonical isolated form  v = rhs/c_v - sum_{u!=v} (c_u/c_v) u ; shared vars
    // with IDENTICAL canonical forms are entailed equal. Reason = the two defining
    // atoms only (the other vars cancel, so they need not appear). SOUND: v1=F and
    // v2=F entail v1=v2 from exactly those two atoms; an entailed equality only
    // aids N-O completeness, never a wrong verdict.
    {
        std::unordered_map<std::string, SharedTermId> nameToShared;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            if (const auto* st = sharedTermRegistry_->get(stId)) {
                if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;  // consts handled by fixed-value grouping
            }
            std::string nm = getVarNameForSharedTerm(stId);
            if (!nm.empty()) nameToShared.emplace(nm, stId);
        }
        // canonical isolated-form key -> [(sharedVar, defining-atom literal)]
        std::map<std::string, std::vector<std::pair<SharedTermId, SatLit>>> byForm;
        for (const auto& e : theoryTrail_) {
            if (e.isDiseq || !e.value) continue;
            if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
            const auto& p = std::get<LinearAtomPayload>(e.atom.payload);
            if (p.rel != Relation::Eq) continue;
            const auto& terms = p.lhs.terms;  // sorted by var name
            if (terms.size() < 2) continue;   // 2-var handled above; need >=2 here too
            const mpq_class& rhs = p.rhs.asRational();
            for (size_t vi = 0; vi < terms.size(); ++vi) {
                auto sit = nameToShared.find(terms[vi].first);
                if (sit == nameToShared.end()) continue;   // v not shared
                const mpq_class& cv = terms[vi].second;
                if (cv == 0) continue;
                // Canonical key: const rhs/cv, then (u, -c_u/cv) for u != v
                // (terms stay name-sorted with vi removed).
                std::string key = mpq_class(rhs / cv).get_str();
                key.push_back('|');
                for (size_t ui = 0; ui < terms.size(); ++ui) {
                    if (ui == vi) continue;
                    key += terms[ui].first;
                    key.push_back(':');
                    key += mpq_class(-terms[ui].second / cv).get_str();
                    key.push_back(';');
                }
                byForm[key].push_back({sit->second, e.lit});
            }
        }
        // REPRESENTATIVE-based emission (NOT pairwise): publish only v = rep for
        // each non-rep bucket member, O(g) instead of O(g^2). EUF /
        // SharedEqualityManager transitive closure derives the remaining
        // member-member equalities (v1=rep, v2=rep => v1=v2). Each v=rep stays
        // soundly explained by the two defining atoms. This is an interim N-O
        // completeness step; the production design is demand-driven (Array posts
        // a (storeIndex,readIndex) ProveEq demand, this oracle answers only that
        // pair) — see [[project_array_reasoning]].
        for (auto& [key, group] : byForm) {
            (void)key;
            if (group.size() < 2) continue;
            const auto& rep = group.front();
            for (size_t k = 1; k < group.size(); ++k) {
                if (group[k].first == rep.first) continue;  // same shared term
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    group[k].first, rep.first,
                    std::vector<SatLit>{group[k].second, rep.second}});
            }
        }
    }

    return result;
}

std::vector<TheorySolver::SharedEqualityPropagation>
LiaSolver::deduceIndexEqualitiesByGaussian(const std::vector<SharedTermId>& idxTerms) {
    std::vector<TheorySolver::SharedEqualityPropagation> result;
    if (!sharedTermRegistry_ || idxTerms.size() < 2) return result;

    // Map each shared array-index term to its simplex var NAME (skip constants).
    std::vector<std::pair<SharedTermId, std::string>> idxVars;
    for (SharedTermId s : idxTerms) {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;
        }
        std::string nm = getVarNameForSharedTerm(s);
        if (!nm.empty()) idxVars.push_back({s, nm});
    }
    if (idxVars.size() < 2) return result;

    // Coordinate space: 0 = ONE (constant), 1.. = variables by name. Each asserted
    // equality `sum c_v v = r` becomes the homogeneous form `sum c_v v - r*ONE = 0`.
    std::unordered_map<std::string, int> varCoord;
    auto coordOf = [&](const std::string& nm) -> int {
        auto it = varCoord.find(nm);
        if (it != varCoord.end()) return it->second;
        int c = static_cast<int>(varCoord.size()) + 1;  // 0 reserved for ONE
        varCoord[nm] = c;
        return c;
    };

    struct Row { std::map<int, mpq_class> coeffs; std::vector<SatLit> reason; };
    std::vector<Row> rows;
    for (const auto& e : theoryTrail_) {
        if (e.isDiseq || !e.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
        const auto& p = std::get<LinearAtomPayload>(e.atom.payload);
        if (p.rel != Relation::Eq) continue;
        Row r;
        for (const auto& t : p.lhs.terms)
            if (t.second != 0) r.coeffs[coordOf(t.first)] += t.second;
        const mpq_class& rhs = p.rhs.asRational();
        if (rhs != 0) r.coeffs[0] += -rhs;   // ONE coord
        for (auto it = r.coeffs.begin(); it != r.coeffs.end(); )
            (it->second == 0) ? it = r.coeffs.erase(it) : ++it;
        if (r.coeffs.empty()) continue;
        r.reason.push_back(e.lit);
        rows.push_back(std::move(r));
    }
    if (rows.empty()) return result;

    // Forward-eliminate to row echelon, keyed by leading (smallest) coord; each
    // pivot is normalized to lead-coeff 1 and carries the reasons of the atoms
    // combined into it. reduce() subtracts pivots from a row, accumulating reasons.
    std::map<int, Row> pivotByLead;
    auto reduce = [&](Row& r) {
        for (;;) {
            int hit = -1;
            for (const auto& kv : r.coeffs)
                if (pivotByLead.count(kv.first)) { hit = kv.first; break; }
            if (hit < 0) break;
            const Row& piv = pivotByLead[hit];
            mpq_class factor = r.coeffs[hit];   // piv lead coeff == 1
            for (const auto& [pc, pv] : piv.coeffs) {
                mpq_class nv = r.coeffs[pc] - factor * pv;
                if (nv == 0) r.coeffs.erase(pc); else r.coeffs[pc] = nv;
            }
            r.reason.insert(r.reason.end(), piv.reason.begin(), piv.reason.end());
        }
    };
    for (auto& row : rows) {
        reduce(row);
        if (row.coeffs.empty()) continue;  // redundant (already spanned)
        int lc = row.coeffs.begin()->first;
        mpq_class lcoeff = row.coeffs[lc];
        if (lcoeff != 1) for (auto& [c, v] : row.coeffs) v /= lcoeff;
        pivotByLead[lc] = std::move(row);
    }

    auto dedupReasons = [](std::vector<SatLit>& rs) {
        std::sort(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        rs.erase(std::unique(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), rs.end());
    };

    // For each array-index pair, test whether (a - b) reduces to the zero form:
    // if so, a = b is entailed by the combining atoms (the accumulated reasons).
    for (size_t i = 0; i < idxVars.size(); ++i) {
        for (size_t j = i + 1; j < idxVars.size(); ++j) {
            if (idxVars[i].second == idxVars[j].second) continue;
            Row target;
            target.coeffs[coordOf(idxVars[i].second)] += 1;
            target.coeffs[coordOf(idxVars[j].second)] += -1;
            for (auto it = target.coeffs.begin(); it != target.coeffs.end(); )
                (it->second == 0) ? it = target.coeffs.erase(it) : ++it;
            reduce(target);
            if (!target.coeffs.empty()) continue;  // a-b not entailed 0
            dedupReasons(target.reason);
            if (target.reason.empty()) continue;   // defensive: need a reason
            result.push_back(TheorySolver::SharedEqualityPropagation{
                idxVars[i].first, idxVars[j].first, std::move(target.reason)});
        }
    }
    return result;
}

std::vector<SatLit> LiaSolver::allActiveReasons() const {
    std::vector<SatLit> rs;
    rs.reserve(theoryTrail_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    for (const auto& e : theoryTrail_) {
        rs.push_back(e.lit);
    }
    for (const auto& ieq : interfaceEqualities_) {
        rs.push_back(ieq.reason);
    }
    for (const auto& idiseq : interfaceDisequalities_) {
        rs.push_back(idiseq.reason);
    }
    std::sort(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    rs.erase(std::unique(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), rs.end());
    return rs;
}

void LiaSolver::allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);
    diseqBranchAuthorized_.insert(key);
}

std::optional<RealValue> LiaSolver::sharedTermArithValue(SharedTermId s) const {
    if (!sharedTermRegistry_ || !coreIr_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = coreIr_->get(st->coreExpr);
    if (expr.kind == Kind::ConstInt) {
        if (auto* iv = std::get_if<int64_t>(&expr.payload.value))
            return RealValue::fromMpq(mpq_class(*iv));
        if (auto* sv = std::get_if<std::string>(&expr.payload.value))
            return RealValue::fromMpq(mpqFromString(*sv));  // large literal (string payload)
    }
    if (expr.kind == Kind::ConstReal) {
        if (auto* sv = std::get_if<std::string>(&expr.payload.value))
            return RealValue::fromMpq(mpqFromString(*sv));
    }
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        return std::nullopt;
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    // Keep shared-term values consistent with a repaired integer model if one
    // was produced (defensive — repair is gated off when interface constraints
    // are active, so this normally never differs from gs_).
    if (repairModel_) {
        auto it = repairModel_->find(name);
        if (it != repairModel_->end()) return RealValue::fromMpq(it->second);
    }
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;
    DeltaRational val = gs_.value(idx);
    // Integer model values are integral after check(); the delta part is an
    // infinitesimal that does not affect the integer comparison.
    return RealValue::fromMpq(val.a);
}

} // namespace xolver
