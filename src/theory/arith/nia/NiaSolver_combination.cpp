#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include "theory/arith/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/nia/search/NiaIcpAdapter.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/nra/nla/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/nia/farkas/FarkasOrModelAssembler.h"
#include "util/MpqUtils.h"
#include <chrono>
#include <iostream>

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

TheoryCheckResult NiaSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    // Phase D: interface eq changes the combined-state signature.
    dispatchCacheValid_ = false;
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Eq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    if (ifaceLifecycleEnabled_) {
        // Keep the interface equality OUT of active_/trail_/activeSet_; record
        // it (with its converted constraint) for level-correct backtracking and
        // for merge at stageNormalize. See member doc on ifaceLifecycleEnabled_.
        interfaceEqualities_.push_back({a, b, reason, level, cc.diff, Relation::Eq});
        return TheoryCheckResult::consistent();
    }
    size_t oldSize = active_.size();
    active_.push_back({cc.diff, Relation::Eq, reason});
    trail_.push_back({level, oldSize});
    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    // Phase D: interface diseq changes the combined-state signature.
    dispatchCacheValid_ = false;
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Neq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    if (ifaceLifecycleEnabled_) {
        interfaceDisequalities_.push_back({a, b, reason, level, cc.diff, Relation::Neq});
        return TheoryCheckResult::consistent();
    }
    size_t oldSize = active_.size();
    active_.push_back({cc.diff, Relation::Neq, reason});
    trail_.push_back({level, oldSize});
    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::optional<RealValue>
NiaSolver::sharedTermArithValue(SharedTermId s) const {
    // Gated default-ON for QF_ANIA / QF_AUFNIA: without this, the combination
    // layer's model-based arrangement (TheoryManager §4) skips every shared
    // term because the loop's `if (!v) continue;` fires when the arith solver
    // returns nullopt (the inherited base default). Closing this gap is what
    // lets array combination ever emit a same-value scalar-arrangement split
    // for QF_ANIA cases (the long-standing 0/157 hole — iter#1-#4 emitted
    // shared-eqs into a layer that wasn't running). Opt-out via
    // XOLVER_NIA_SHARED_ARITH_VALUE=0 if the arrangement+nonlinear-branch
    // interaction starts to oscillate.
    static const bool enabled =
        env::paramInt("XOLVER_NIA_SHARED_ARITH_VALUE", 1) != 0;
    if (!enabled) return std::nullopt;

    if (!sharedTermRegistry_ || !coreIr_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = coreIr_->get(st->coreExpr);

    // Constants — return the literal value directly. Mirrors LiaSolver's
    // constant handling so an arithmetic constant participates in the
    // arrangement on equal terms with a variable bound to that value.
    if (expr.kind == Kind::ConstInt) {
        if (auto* iv = std::get_if<int64_t>(&expr.payload.value)) {
            return RealValue::fromMpq(mpq_class(*iv));
        }
        if (auto* sv = std::get_if<std::string>(&expr.payload.value)) {
            return RealValue::fromMpq(mpqFromString(*sv));
        }
    }
    if (expr.kind == Kind::ConstReal) {
        if (auto* sv = std::get_if<std::string>(&expr.payload.value)) {
            return RealValue::fromMpq(mpqFromString(*sv));
        }
    }

    // Variables — read the latest NIA model entry. currentModel_ holds the
    // current check()'s candidate model; lastValidatedFarkasModel_ is the
    // fallback Farkas-Or witness that survives reset/backtrack. Either is
    // sound for the arrangement's "what value does NIA think this term has
    // right now?" query — the arrangement only emits TAUTOLOGY splits
    // `(a = b) ∨ ¬(a = b)`, so a wrong-guess split costs one SAT-layer commit
    // cycle but never a soundness violation. ModelValidator at the
    // Solver::Impl boundary still catches a globally-inconsistent model.
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        // Iter#30: compound shared terms (e.g. `(+ i 1)` as an array index)
        // had no value path here pre-iter#30 — returned nullopt → array-
        // combination arrangement skipped them entirely. iter#28-29 opened
        // the channel; this opens the SOURCE for compound terms by
        // recursively evaluating Add/Sub/Mul/Neg over the current NIA
        // model. SOUND: this only returns a value when EVERY leaf evaluates
        // (Variable found in model, Const literal); on any unresolved leaf
        // or unsupported kind, falls through to nullopt → arrangement
        // safely skips the term (same as pre-iter#30 behavior).
        // Recursion depth bounded at 32 (anti-pathological-DAG guard).
        const IntegerModel* src = nullptr;
        if (currentModel_)                  src = &*currentModel_;
        else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
        if (!src) return std::nullopt;
        std::function<std::optional<mpz_class>(ExprId, int)> ev =
            [&](ExprId e, int depth) -> std::optional<mpz_class> {
                if (depth > 32 || e == NullExpr || e >= coreIr_->size())
                    return std::nullopt;
                const auto& n = coreIr_->get(e);
                if (n.kind == Kind::ConstInt) {
                    if (auto* iv = std::get_if<int64_t>(&n.payload.value))
                        return mpz_class(*iv);
                    if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
                        try { return mpz_class(*sv); }
                        catch (...) { return std::nullopt; }
                    }
                    return std::nullopt;
                }
                if (n.kind == Kind::Variable) {
                    if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                        auto it = src->find(*nm);
                        if (it == src->end()) return std::nullopt;
                        return it->second;
                    }
                    return std::nullopt;
                }
                if (n.kind == Kind::Add) {
                    mpz_class acc = 0;
                    for (ExprId c : n.children) {
                        auto cv = ev(c, depth + 1);
                        if (!cv) return std::nullopt;
                        acc += *cv;
                    }
                    return acc;
                }
                if (n.kind == Kind::Sub) {
                    if (n.children.empty()) return std::nullopt;
                    auto fv = ev(n.children[0], depth + 1);
                    if (!fv) return std::nullopt;
                    mpz_class acc = *fv;
                    for (size_t i = 1; i < n.children.size(); ++i) {
                        auto cv = ev(n.children[i], depth + 1);
                        if (!cv) return std::nullopt;
                        acc -= *cv;
                    }
                    return acc;
                }
                if (n.kind == Kind::Neg) {
                    if (n.children.size() != 1) return std::nullopt;
                    auto cv = ev(n.children[0], depth + 1);
                    if (!cv) return std::nullopt;
                    return -*cv;
                }
                if (n.kind == Kind::Mul) {
                    mpz_class acc = 1;
                    for (ExprId c : n.children) {
                        auto cv = ev(c, depth + 1);
                        if (!cv) return std::nullopt;
                        acc *= *cv;
                    }
                    return acc;
                }
                return std::nullopt;
            };
        auto val = ev(st->coreExpr, 0);
        if (!val) return std::nullopt;
        return RealValue::fromMpz(*val);
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    const IntegerModel* src = nullptr;
    if (currentModel_)                  src = &*currentModel_;
    else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
    // Iter#25 diag: count ALL invocations + classification (null-model vs
    // found vs missing-from-model). Set XOLVER_NIA_ARITH_VALUE_DIAG=1.
    static const bool diag =
        xolver::env::diag("XOLVER_NIA_ARITH_VALUE_DIAG");
    static long callCount = 0;
    static long nullModelCount = 0;
    static long missingNameCount = 0;
    static long foundCount = 0;
    if (diag) {
        ++callCount;
        if (!src) ++nullModelCount;
        else if (src->find(name) == src->end()) ++missingNameCount;
        else ++foundCount;
        if (callCount % 100 == 1) {
            std::fprintf(stderr,
                         "[NIA-ARITH-VALUE] calls=%ld null-model=%ld missing-name=%ld found=%ld\n",
                         callCount, nullModelCount, missingNameCount, foundCount);
        }
    }
    if (!src) return std::nullopt;
    auto it = src->find(name);
    if (it == src->end()) return std::nullopt;
    return RealValue::fromMpz(it->second);
}

std::vector<TheorySolver::SharedEqualityPropagation>
NiaSolver::getDeducedSharedEqualities() {
    // Nelson-Oppen fixed-value seam: when two shared integer variables both
    // have their NIA domain pinned to the same singleton {v}, propagate the
    // equality to EUF so the e-graph can fire array/UF axioms (read-over-
    // write, congruence) that depend on the equality.
    //
    // Without this, QF_ANIA / QF_AUFNIA combination instances where the
    // equality is implied by NIA bounds (e.g. `a = b` follows from
    // `a >= n /\ a <= n /\ b >= n /\ b <= n`) are unreachable: NIA never
    // tells EUF, EUF never closes the read-over-write, and the combined
    // verdict stays Unknown. NiaSolver previously returned {} unconditionally,
    // closing this seam entirely (the LIA path was the only one open).
    //
    // SOUND: a pair is emitted only when both vars' integer domains pin them
    // to the same value, and the propagation reasons are the (deduped) union
    // of the four bound-reason literals (lo_a, hi_a, lo_b, hi_b). If any
    // bound is later relaxed by backtrack, the propagation's reason becomes
    // unsatisfied and the SAT layer retracts it through normal conflict
    // analysis. Same proof contract as LiaSolver::getDeducedSharedEqualities'
    // fixed-value loop.
    if (!sharedTermRegistry_) return {};

    struct Entry {
        SharedTermId stId;
        std::vector<SatLit> reasons;
    };
    // map<mpz_class, ...> for determinism (autotuner / oracle reproducibility).
    std::map<mpz_class, std::vector<Entry>> groups;

    for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
        std::string name = getVarNameForSharedTerm(stId);
        if (name.empty()) continue;
        const IntDomain* d = domains_.getDomain(name);
        if (!d) continue;
        if (!(d->hasLower && d->hasUpper)) continue;
        if (d->lower.value != d->upper.value) continue;

        std::vector<SatLit> reasons;
        reasons.insert(reasons.end(), d->lower.reasons.begin(),
                       d->lower.reasons.end());
        reasons.insert(reasons.end(), d->upper.reasons.begin(),
                       d->upper.reasons.end());
        std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end(),
                                  [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), reasons.end());

        groups[d->lower.value].push_back({stId, std::move(reasons)});
    }

    std::vector<TheorySolver::SharedEqualityPropagation> result;
    for (auto& [val, entries] : groups) {
        if (entries.size() < 2) continue;
        for (size_t i = 0; i < entries.size(); ++i) {
            for (size_t j = i + 1; j < entries.size(); ++j) {
                std::vector<SatLit> combined;
                combined.insert(combined.end(), entries[i].reasons.begin(),
                                entries[i].reasons.end());
                combined.insert(combined.end(), entries[j].reasons.begin(),
                                entries[j].reasons.end());
                std::sort(combined.begin(), combined.end(),
                          [](SatLit a, SatLit b) {
                    return a.var < b.var || (a.var == b.var && a.sign < b.sign);
                });
                combined.erase(std::unique(combined.begin(), combined.end(),
                                           [](SatLit a, SatLit b) {
                    return a.var == b.var && a.sign == b.sign;
                }), combined.end());
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    entries[i].stId, entries[j].stId, std::move(combined)});
            }
        }
    }

    // ---------------------------------------------------------------------
    // Var-var implied equalities (port of LIA's assertedVarEqualityReason).
    //
    // Two shared integer variables can be forced equal by NIA-asserted
    // linear atoms even when neither domain pins to a constant: an explicit
    // equality atom `c*x - c*y = k` with `k = 0`, or complementary
    // inequalities `c*(x-y) >= k AND c*(x-y) <= k` collapsing to a single
    // point. For each pair of shared vars (a, b), walk the active trail
    // accumulating bounds on `d = na - nb` from atoms whose polynomial is
    // exactly a 2-variable linear difference; if the accumulated interval
    // collapses to {0}, emit the propagation with the two pinning literals.
    //
    // SOUND:
    //   1. Exact-pins-only: only emit when the accumulated lo == up == 0
    //      after iterating all 2-var difference atoms on the trail. Strict
    //      bounds (Lt/Gt) are skipped (they don't pin an equality).
    //   2. Complete explanation: reasons = the two pinning literals (loLit,
    //      upLit) — those are the SAT literals whose retraction unblocks
    //      the derived equality. SAT-CDCL will retract the propagation
    //      automatically when either reason becomes unassigned.
    //   3. Backtrack invalidation: state_.trail entries are dropped by the
    //      base class's backtrackToLevel; the next getDeducedSharedEqualities
    //      call rescans fresh.
    //   4. Deduped against the fixed-value loop above (a pair already pinned
    //      by both vars being singleton-domain is not re-emitted here).
    //   5. PolynomialAtomPayload with an algebraic (non-rational) rhs is
    //      skipped — over-conservative but never wrong.
    if (sharedTermRegistry_) {
        struct SV { SharedTermId stId; std::string name; };
        std::vector<SV> svs;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            std::string name = getVarNameForSharedTerm(stId);
            if (name.empty()) continue;
            svs.push_back({stId, std::move(name)});
        }

        if (svs.size() >= 2) {
            auto pairKey = [](SharedTermId a, SharedTermId b) -> uint64_t {
                SharedTermId lo = a < b ? a : b;
                SharedTermId hi = a < b ? b : a;
                return (static_cast<uint64_t>(lo) << 32)
                     | static_cast<uint32_t>(hi);
            };
            std::unordered_set<uint64_t> emittedPair;
            for (const auto& p : result) emittedPair.insert(pairKey(p.a, p.b));

            // name -> svs index (only shared-term names are keys).
            std::unordered_map<std::string, size_t> nameToIdx;
            nameToIdx.reserve(svs.size() * 2);
            for (size_t i = 0; i < svs.size(); ++i) nameToIdx.emplace(svs[i].name, i);

            // Per-pair accumulator of bounds on d = na - nb (na = the smaller-svs-
            // index shared var). SINGLE trail pass: each 2-var linear-difference
            // atom is analysed ONCE (one kernel_->variables / kernel_->terms call)
            // and bucketed into its var pair — O(trail), versus the prior
            // O(shared_vars^2 * trail) which re-ran the allocating libpoly
            // variables() call for every (i,j) pair (the cs_* QF_ANIA hot path:
            // ~100 shared vars * ~500 trail atoms * 5 checks = millions of libpoly
            // calls -> the wall). Behaviour-identical: same tightest-bound
            // accumulation, same trail-order tie-breaking, same pin test, same
            // svs-index emission order.
            struct Acc {
                bool haveLo = false, haveUp = false;
                mpq_class lo = 0, up = 0;
                SatLit loLit{}, upLit{};
            };
            std::map<std::pair<size_t, size_t>, Acc> acc;  // key = (ia<ib) -> bounds

            for (const auto& e : state_.trail) {
                const auto* p = std::get_if<PolynomialAtomPayload>(&e.atom.payload);
                if (!p) continue;
                if (!p->rhs.isRational()) continue;

                auto vars = kernel_->variables(p->poly);
                if (vars.size() != 2) continue;
                auto it0 = nameToIdx.find(vars[0]);
                auto it1 = nameToIdx.find(vars[1]);
                if (it0 == nameToIdx.end() || it1 == nameToIdx.end()) continue;
                size_t ia = it0->second, ib = it1->second;
                if (ia == ib) continue;
                if (ia > ib) std::swap(ia, ib);          // na = svs[ia] (smaller idx)
                if (emittedPair.count(pairKey(svs[ia].stId, svs[ib].stId))) continue;
                const std::string& na = svs[ia].name;
                const std::string& nb = svs[ib].name;

                auto tOpt = kernel_->terms(p->poly);
                if (!tOpt) continue;
                mpz_class cA = 0, cB = 0, k = 0;
                bool ok = true;
                for (const auto& m : *tOpt) {
                    if (m.powers.empty()) {
                        k += m.coefficient;
                    } else if (m.powers.size() == 1 && m.powers[0].second == 1) {
                        std::string vn(kernel_->varName(m.powers[0].first));
                        if (vn == na)      cA += m.coefficient;
                        else if (vn == nb) cB += m.coefficient;
                        else { ok = false; break; }
                    } else {
                        ok = false; break;  // nonlinear monomial
                    }
                }
                if (!ok) continue;
                if (cA == 0 || cA != -cB) continue;

                Relation rel = e.value ? p->rel : negateRelation(p->rel);
                if (rel == Relation::Neq) continue;  // never pins
                const mpq_class& rhsQ = p->rhs.asRational();
                // poly = cA*(na - nb) + k ; rel rhsQ  =>  d = na-nb : cA*d rel (rhsQ-k)
                mpq_class bnd = (rhsQ - mpq_class(k)) / mpq_class(cA);
                bool flip = (cA < 0);
                Acc& a = acc[{ia, ib}];
                auto addLower = [&](const mpq_class& v, SatLit lit) {
                    if (!a.haveLo || v > a.lo) { a.lo = v; a.loLit = lit; a.haveLo = true; }
                };
                auto addUpper = [&](const mpq_class& v, SatLit lit) {
                    if (!a.haveUp || v < a.up) { a.up = v; a.upLit = lit; a.haveUp = true; }
                };
                switch (rel) {
                    case Relation::Eq:
                        addLower(bnd, e.lit); addUpper(bnd, e.lit); break;
                    case Relation::Leq:
                        if (!flip) addUpper(bnd, e.lit); else addLower(bnd, e.lit); break;
                    case Relation::Geq:
                        if (!flip) addLower(bnd, e.lit); else addUpper(bnd, e.lit); break;
                    case Relation::Lt:
                    case Relation::Gt:
                    default:
                        break;  // strict — does not pin
                }
            }

            // std::map iterates keys (ia, ib) in ascending order == the prior
            // nested-loop's (i, j) emission order.
            for (auto& [key, a] : acc) {
                if (!(a.haveLo && a.haveUp && a.lo == 0 && a.up == 0)) continue;
                std::vector<SatLit> reasons;
                reasons.push_back(a.loLit);
                if (!(a.upLit == a.loLit)) reasons.push_back(a.upLit);
                std::sort(reasons.begin(), reasons.end(), [](SatLit x, SatLit y) {
                    return x.var < y.var || (x.var == y.var && x.sign < y.sign);
                });
                reasons.erase(std::unique(reasons.begin(), reasons.end(),
                                          [](SatLit x, SatLit y) {
                    return x.var == y.var && x.sign == y.sign;
                }), reasons.end());
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    svs[key.first].stId, svs[key.second].stId, std::move(reasons)});
            }
        }
    }

    // Iter#25 diag: count ALL invocations + propagation sizes. Set
    // XOLVER_NIA_SHARED_EQ_DIAG=1 to see periodic counter. This proves
    // master directive #1: does NIA emit shared-eqs at all on QF_ANIA?
    static long callCount = 0;
    static long totalEmitted = 0;
    if (xolver::env::diag("XOLVER_NIA_SHARED_EQ_DIAG")) {
        ++callCount;
        totalEmitted += result.size();
        if (callCount % 20 == 1 || !result.empty()) {
            std::fprintf(stderr,
                         "[NIA-SHARED-EQ] calls=%ld emitted-this=%zu total=%ld\n",
                         callCount, result.size(), totalEmitted);
        }
    }
    return result;
}

std::optional<std::vector<SatLit>>
NiaSolver::proveSharedDisjoint(SharedTermId a, SharedTermId b) {
    // L5 demand-driven disequality: a,b are provably unequal iff their integer
    // domains do not overlap. SOUND + complete reason:
    //   a.upper < b.lower  =>  (a ≤ a.upper) ∧ (b ≥ b.lower) entail a < b ⟹ a≠b
    // so the reason is exactly {a's upper-bound literals, b's lower-bound
    // literals} (or the symmetric pair). Backtracking either bound retracts the
    // disequality via normal SAT conflict analysis. Same domain/bound-reason
    // contract as the fixed-value equality producer.
    if (!sharedTermRegistry_) return std::nullopt;
    std::string na = getVarNameForSharedTerm(a);
    std::string nb = getVarNameForSharedTerm(b);
    if (na.empty() || nb.empty()) return std::nullopt;

    // (1) ABSOLUTE disjoint domains: a.upper < b.lower (or symmetric).
    const IntDomain* da = domains_.getDomain(na);
    const IntDomain* db = domains_.getDomain(nb);
    if (da && db && da->hasLower && da->hasUpper && db->hasLower && db->hasUpper) {
        const IntDomain* lo = nullptr;  // lower interval (its upper separates)
        const IntDomain* hi = nullptr;  // higher interval (its lower separates)
        if (da->upper.value < db->lower.value)      { lo = da; hi = db; }
        else if (db->upper.value < da->lower.value) { lo = db; hi = da; }
        if (lo) {
            std::vector<SatLit> reasons;
            reasons.insert(reasons.end(), lo->upper.reasons.begin(),
                           lo->upper.reasons.end());
            reasons.insert(reasons.end(), hi->lower.reasons.begin(),
                           hi->lower.reasons.end());
            if (!reasons.empty()) {
                std::sort(reasons.begin(), reasons.end(), [](SatLit x, SatLit y) {
                    return x.var < y.var || (x.var == y.var && x.sign < y.sign);
                });
                reasons.erase(std::unique(reasons.begin(), reasons.end(),
                                          [](SatLit x, SatLit y) {
                    return x.var == y.var && x.sign == y.sign;
                }), reasons.end());
                return reasons;
            }
        }
    }

    // (2) VAR-VAR DIFFERENCE: d = na - nb forced AWAY from 0 by a 2-variable
    // linear difference atom on the trail (the BMC index case: i = j+c with c!=0,
    // i >= j+1, i != j, ...). Port of the var-var EQUALITY detector in
    // getDeducedSharedEqualities, but checking 0-EXCLUSION instead of 0-pin.
    //   d >= lo with lo > 0  =>  d > 0  => na != nb   (reason = the one lo atom)
    //   d <= up with up < 0  =>  d < 0  => na != nb   (reason = the one up atom)
    //   d != 0 directly                 => na != nb   (reason = that atom)
    // Each is justified by a SINGLE asserted literal (complete: that literal
    // entails the strict direction independent of the rest of the trail).
    if (!kernel_) return std::nullopt;
    bool haveLo = false, haveUp = false;
    mpq_class lo = 0, up = 0;
    SatLit loLit{}, upLit{};
    for (const auto& e : state_.trail) {
        const auto* p = std::get_if<PolynomialAtomPayload>(&e.atom.payload);
        if (!p || !p->rhs.isRational()) continue;
        auto vars = kernel_->variables(p->poly);
        if (vars.size() != 2) continue;
        bool hasA = false, hasB = false;
        for (const auto& v : vars) { if (v == na) hasA = true; else if (v == nb) hasB = true; }
        if (!hasA || !hasB) continue;
        auto tOpt = kernel_->terms(p->poly);
        if (!tOpt) continue;
        mpz_class cA = 0, cB = 0, k = 0;
        bool ok = true;
        for (const auto& m : *tOpt) {
            if (m.powers.empty()) { k += m.coefficient; }
            else if (m.powers.size() == 1 && m.powers[0].second == 1) {
                std::string vn(kernel_->varName(m.powers[0].first));
                if (vn == na)      cA += m.coefficient;
                else if (vn == nb) cB += m.coefficient;
                else { ok = false; break; }
            } else { ok = false; break; }   // nonlinear monomial
        }
        if (!ok) continue;
        if (cA == 0 || cA != -cB) continue;   // not c*(na - nb) + k
        Relation rel = e.value ? p->rel : negateRelation(p->rel);
        const mpq_class& rhsQ = p->rhs.asRational();
        // poly = cA*(na - nb) + k  rel  rhsQ   =>   d  rel'  (rhsQ - k)/cA
        mpq_class bnd = (rhsQ - mpq_class(k)) / mpq_class(cA);
        bool flip = (cA < 0);
        if (rel == Relation::Neq) {
            if (bnd == 0) return std::vector<SatLit>{e.lit};   // d != 0 directly
            continue;
        }
        auto addLower = [&](const mpq_class& v, SatLit lit) {
            if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
        };
        auto addUpper = [&](const mpq_class& v, SatLit lit) {
            if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
        };
        // d = na - nb is an integer, so a strict bound tightens by one step:
        //   d > bnd  => d >= floor(bnd)+1   ;   d < bnd  => d <= ceil(bnd)-1
        // (without this, "i > j" with bnd=0 would record lo=0 and miss d>0).
        auto floorQ = [](const mpq_class& q) {
            mpz_class r; mpz_fdiv_q(r.get_mpz_t(), q.get_num_mpz_t(),
                                    q.get_den_mpz_t()); return r;
        };
        auto ceilQ = [](const mpq_class& q) {
            mpz_class r; mpz_cdiv_q(r.get_mpz_t(), q.get_num_mpz_t(),
                                    q.get_den_mpz_t()); return r;
        };
        mpq_class loStrict(floorQ(bnd) + 1);   // d > bnd  => d >= loStrict
        mpq_class upStrict(ceilQ(bnd) - 1);    // d < bnd  => d <= upStrict
        switch (rel) {
            case Relation::Eq:  addLower(bnd, e.lit); addUpper(bnd, e.lit); break;
            case Relation::Leq:
                if (flip) addLower(bnd, e.lit); else addUpper(bnd, e.lit); break;
            case Relation::Geq:
                if (flip) addUpper(bnd, e.lit); else addLower(bnd, e.lit); break;
            case Relation::Lt:
                if (flip) addLower(loStrict, e.lit); else addUpper(upStrict, e.lit);
                break;
            case Relation::Gt:
                if (flip) addUpper(upStrict, e.lit); else addLower(loStrict, e.lit);
                break;
            default: break;
        }
    }
    if (haveLo && lo > 0) return std::vector<SatLit>{loLit};   // d >= lo > 0
    if (haveUp && up < 0) return std::vector<SatLit>{upLit};   // d <= up < 0
    return std::nullopt;
}

std::optional<TheorySolver::TheoryModel> NiaSolver::getModel() const {
    // Prefer currentModel_; fall back to lastValidatedFarkasModel_ which
    // survives reset()/backtrack and represents the last validator-
    // confirmed Farkas-Or witness. Used by Solver.cpp's Unknown-fallback
    // to recover a SAT verdict when SAT-CDCL timed out.
    const IntegerModel* src = nullptr;
    if (currentModel_)               src = &*currentModel_;
    else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
    if (!src) return std::nullopt;
    TheoryModel model;
    for (const auto& [name, value] : *src) {
        model.assignments[name] = value.get_str();
        model.numericAssignments.insert({name, RealValue::fromMpz(value)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

} // namespace xolver
