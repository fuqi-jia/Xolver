#include "util/MpqUtils.h"
#include "theory/arith/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "theory/combination/CareGraph.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace zolver {

LiaSolver::LiaSolver() {
    const char* env = std::getenv("ZOLVER_LIA_DUMP_DIR");
    if (env) {
        dumpCounter_ = 0;
    }
    // Phase 2: single core reasoner (incremental replay + interface eqs +
    // simplex + integrality + branch).
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "lia.core",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCore(db, e); }));
}

LiaSolver::~LiaSolver() {
#ifdef ZOLVER_LIA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
#endif
}

void LiaSolver::onPush() {
    gs_.push();
}

void LiaSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LiaSolver::onReset() {
    theoryTrail_.clear();
    appliedCursor_ = 0;
    activeAtoms_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    diseqBranchAuthorized_.clear();
    gs_.resetActiveBounds();
}

void LiaSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    const auto& payload = std::get<LinearAtomPayload>(atom.payload);
    // LIA bounds are rational (integer-theory inputs never produce algebraic
    // RHS); asRational() is the standard conversion at this boundary.
    const mpq_class& rhs = payload.rhs.asRational();
    int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, rhs);
    Relation effectiveRel = value ? payload.rel : negateRelation(payload.rel);
    bool isDiseq = (effectiveRel == Relation::Neq);

    for (auto& e : theoryTrail_) {
        if (e.atom.satVar == atom.satVar) {
            if (e.isDiseq) {
                auto it = std::remove_if(disequalities_.begin(), disequalities_.end(),
                    [&e](const auto& d) { return d.lit == e.lit; });
                disequalities_.erase(it, disequalities_.end());
            } else {
                auto it = std::remove_if(activeAtoms_.begin(), activeAtoms_.end(),
                    [&e](const auto& a) { return a.lit == e.lit; });
                activeAtoms_.erase(it, activeAtoms_.end());
            }
            e = {level, assertedLit, atom, value, auxVar, isDiseq};
            if (isDiseq) {
                disequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit});
            } else {
                activeAtoms_.push_back({atom.exprId, auxVar, payload.rel, value, payload.lhs, rhs, assertedLit});
            }
            return;
        }
    }
    theoryTrail_.push_back({level, assertedLit, atom, value, auxVar, isDiseq});
    if (isDiseq) {
        disequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit});
    } else {
        activeAtoms_.push_back({atom.exprId, auxVar, payload.rel, value, payload.lhs, rhs, assertedLit});
    }
}

void LiaSolver::onBacktrack(int level) {
    currentLevel_ = level;
    if (level == 0) {
        gs_.resetActiveBounds();
    } else {
        gs_.backtrackToLevel(level);
    }

    if (level == 0) {
        // Full reset for modelCheck rebuild or SAT restart to level 0.
        // All entries will be re-asserted by the caller.
        theoryTrail_.clear();
        disequalities_.clear();
        activeAtoms_.clear();
        interfaceEqualities_.clear();
        interfaceDisequalities_.clear();
    } else {
        while (!theoryTrail_.empty() && theoryTrail_.back().level > level) {
            const auto& e = theoryTrail_.back();
            if (e.isDiseq) {
                auto it = std::remove_if(disequalities_.begin(), disequalities_.end(),
                    [&e](const auto& d) { return d.lit == e.lit; });
                disequalities_.erase(it, disequalities_.end());
            } else {
                auto it = std::remove_if(activeAtoms_.begin(), activeAtoms_.end(),
                    [&e](const auto& a) { return a.lit == e.lit; });
                activeAtoms_.erase(it, activeAtoms_.end());
            }
            theoryTrail_.pop_back();
        }
        auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

        auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
    }
    if (appliedCursor_ > theoryTrail_.size()) {
        appliedCursor_ = theoryTrail_.size();
    }
}

std::optional<TheoryCheckResult> LiaSolver::stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    pendingConflict_.reset();

#ifdef ZOLVER_LIA_PROFILE
    profile_.checkCalls++;
    int currentActive = static_cast<int>(theoryTrail_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    profile_.totalActiveLiterals += currentActive;
    if (currentActive > profile_.maxActiveLiterals) profile_.maxActiveLiterals = currentActive;
    profile_.totalNewLiterals += std::max(0, currentActive - profile_.prevActiveCount);
    profile_.prevActiveCount = currentActive;
    auto prof_t0 = std::chrono::steady_clock::now();
#endif

#ifndef ZOLVER_LIA_INCREMENTAL
    // -------------------------------------------------------------------------
    // Full-rebuild mode (baseline for comparison)
    // -------------------------------------------------------------------------
    gs_.resetActiveBounds();
    disequalities_.clear();
    activeAtoms_.clear();
    integerVars_.clear();

    for (const auto& e : theoryTrail_) {
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);

        for (const auto& [name, coeff] : payload.lhs.terms) {
            (void)coeff;
            int v = manager_.getOrCreateVar(gs_, name);
            integerVars_.insert(v);
        }

        if (e.isDiseq) {
            disequalities_.push_back({e.auxVar, payload.lhs, payload.rhs, e.lit});
        } else {
            bool ok = manager_.assertBound(gs_, e.auxVar, payload.rel, e.value, e.lit, e.level);
            if (!ok) {
                pendingConflict_ = PendingConflict{e.level, manager_.translateConflict(gs_)};
                break;
            }
            activeAtoms_.push_back({e.atom.exprId, e.auxVar, payload.rel, e.value, payload.lhs, payload.rhs, e.lit});
        }
    }
#else
    // -------------------------------------------------------------------------
    // Phase 1: incremental replay of new trail entries
    // -------------------------------------------------------------------------
    while (appliedCursor_ < theoryTrail_.size()) {
        const auto& e = theoryTrail_[appliedCursor_];
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);

        if (!e.isDiseq) {
            bool ok = manager_.assertBound(gs_, e.auxVar, payload.rel, e.value, e.lit, e.level);
            if (!ok) {
                pendingConflict_ = PendingConflict{e.level, manager_.translateConflict(gs_)};
                break;
            }
        }

        ++appliedCursor_;
    }
#endif

    if (pendingConflict_) {
#ifdef ZOLVER_LIA_PROFILE
        auto prof_t1 = std::chrono::steady_clock::now();
        profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
        int sz = static_cast<int>(pendingConflict_->conflict.clause.size());
        profile_.totalConflictSize += sz;
        if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
        profile_.immediateConflictCount++;
#endif
        bool ok = normalizeTheoryClause(pendingConflict_->conflict.clause);
        assert(ok && "complementary literal in pending conflict");
        (void)ok;
        if (auto z3r = z3CheckCurrentState(); z3r && *z3r) {
            std::cerr << "[UNSOUND_LIA_LEMMA] pending conflict but Z3 says SAT\n";
            dumpState("unsat_pending_UNSOUND");
            return TheoryCheckResult::unknown();
        }
        dumpState("unsat_pending");
        return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    }

#ifdef ZOLVER_LIA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
    auto prof_t2 = prof_t1;
#endif

#ifdef ZOLVER_LIA_INCREMENTAL
    // Rebuild integerVars_ from activeAtoms_ and disequalities_ (low overhead)
    integerVars_.clear();
    for (const auto& a : activeAtoms_) {
        for (const auto& [name, coeff] : a.lhs.terms) {
            (void)coeff;
            int v = manager_.getOrCreateVar(gs_, name);
            integerVars_.insert(v);
        }
    }
    for (const auto& d : disequalities_) {
        for (const auto& [name, coeff] : d.lhs.terms) {
            (void)coeff;
            int v = manager_.getOrCreateVar(gs_, name);
            integerVars_.insert(v);
        }
    }
#endif

    // Apply interface equalities from Nelson-Oppen combination
    for (const auto& ieq : interfaceEqualities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            bool ok = true;
            ok = gs_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            ok = gs_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                tc.clause.push_back(ieq.reason);
#ifdef ZOLVER_LIA_PROFILE
                auto prof_t3 = std::chrono::steady_clock::now();
                profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t3 - prof_t2).count();
                int sz = static_cast<int>(tc.clause.size());
                profile_.totalConflictSize += sz;
                if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
                profile_.immediateConflictCount++;
#endif
                bool ok = normalizeTheoryClause(tc.clause);
                assert(ok && "complementary literal in IEQ conflict");
                (void)ok;
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    auto r = gs_.check();

#ifdef ZOLVER_LIA_PROFILE
    auto prof_t3 = std::chrono::steady_clock::now();
    profile_.simplexCheckTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t3 - prof_t2).count();
    profile_.totalPivotCount += gs_.pivotCount();
    gs_.resetPivotCount();
    auto cs = gs_.coeffStats();
    profile_.mpqOpTimeUs += cs.mpqOpTimeUs;
    profile_.maxCoeffNumBits = std::max(profile_.maxCoeffNumBits, cs.maxCoeffNumBits);
    profile_.maxCoeffDenBits = std::max(profile_.maxCoeffDenBits, cs.maxCoeffDenBits);
    profile_.totalCoeffNumBits += cs.totalCoeffNumBits;
    profile_.totalCoeffDenBits += cs.totalCoeffDenBits;
    profile_.totalCoeffSamples += cs.totalCoeffSamples;
    gs_.resetCoeffStats();
    auto prof_t4 = prof_t3;
#endif

    if (r == GeneralSimplex::Result::Unsat) {
        auto tc = TheoryConflict{};
        const auto& conflict = gs_.getConflict();
        if (!conflict.empty()) {
            for (const auto& cr : conflict) {
                tc.clause.push_back(cr.reason);
            }
#ifdef ZOLVER_LIA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            if (gs_.hasImmediateConflict()) {
                profile_.immediateConflictCount++;
            } else {
                profile_.rowConflictCount++;
            }
#endif
        } else {
            tc.clause = allActiveReasons();
#ifdef ZOLVER_LIA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.fallbackConflictCount++;
#endif
        }
        bool ok = normalizeTheoryClause(tc.clause);
        assert(ok && "complementary literal in simplex conflict");
        (void)ok;
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // P3: Check interface disequalities. LIA is non-convex; if any
    // interface disequality is provably fixed to 0, we cannot
    // emit a split lemma without arrangement. Return Unknown conservatively.
    // But if aux is not fixed (free variable), LIA has no opinion — let EUF handle it.
    for (const auto& ieq : interfaceDisequalities_) {
        // Direct entailment: an asserted 2-var equality (e.g. (+i1)=(+j1) ⟺
        // i - j = 0) makes i = j, so an interface disequality i != j is a hard
        // conflict. The conflict clause is {asserted-eq-lit, diseq-reason}
        // (both currently true). Caught here before the conservative
        // fixed-value Unknown gate below, turning R4 into a real UNSAT.
        if (auto eqReasons = assertedVarEqualityReason(ieq.a, ieq.b); !eqReasons.empty()) {
            TheoryConflict tc;
            for (auto l : eqReasons) tc.clause.push_back(l);
            tc.clause.push_back(ieq.reason);
            if (normalizeTheoryClause(tc.clause)) {
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            auto fixedOpt = gs_.proveFixedValue(aux);
            if (fixedOpt && fixedOpt->first.isZero()) {
                // The difference x - y is provably pinned to 0 by bounds (e.g.
                // x<=y ∧ y<=x), so x = y is entailed and the interface
                // disequality x != y is a hard conflict. Build the conflict
                // from the pinning bound reasons + the disequality reason
                // (proof-carrying), instead of the old conservative Unknown.
                TheoryConflict tc;
                for (const auto& br : fixedOpt->second) tc.clause.push_back(br.reason);
                tc.clause.push_back(ieq.reason);
                if (normalizeTheoryClause(tc.clause)) {
                    return TheoryCheckResult::mkConflict(std::move(tc));
                }
                // Defensive: if the conflict cannot be normalized (a
                // complementary pair slipped in), fall back to the previous
                // sound-but-incomplete Unknown.
                return TheoryCheckResult::unknown();
            }
            // Honor a DECIDED interface disequality the convex model violates:
            // (a != b) decided but the simplex point happens to set a = b
            // (both free -> defaulted equal). Branch the integer model apart:
            //   (a != b) => (a - b <= -1) OR (a - b >= 1).
            // Only at Full effort (a real model is in hand) and only when both
            // shared terms resolve to simplex variables.
            SharedTermId loK = ieq.a < ieq.b ? ieq.a : ieq.b;
            SharedTermId hiK = ieq.a < ieq.b ? ieq.b : ieq.a;
            uint64_t authKey = (static_cast<uint64_t>(loK) << 32) |
                               static_cast<uint64_t>(hiK);
            if (effort == TheoryEffort::Full && registry_ &&
                !fixedOpt && diseqBranchAuthorized_.count(authKey)) {
                std::string va = getVarNameForSharedTerm(ieq.a);
                std::string vb = getVarNameForSharedTerm(ieq.b);
                if (!va.empty() && !vb.empty() && va != vb &&
                    va.rfind("__const_", 0) != 0 && vb.rfind("__const_", 0) != 0) {
                    DeltaRational d = gs_.value(aux);
                    if (d.a == 0 && d.b == 0) {
                        LinearFormKey form;
                        form.terms.push_back({va, mpq_class(1)});
                        form.terms.push_back({vb, mpq_class(-1)});
                        SatLit litLe = registry_->getOrCreateLinearBoundAtom(
                            form, Relation::Leq, mpq_class(-1), TheoryId::LIA);
                        SatLit litGe = registry_->getOrCreateLinearBoundAtom(
                            form, Relation::Geq, mpq_class(1), TheoryId::LIA);
                        TheoryLemma lemma{{ieq.reason.negated(), litLe, litGe}};
                        if (!lemmaDb.contains(lemma)) {
                            return TheoryCheckResult::mkLemma(std::move(lemma));
                        }
                    }
                }
            }
        }
    }

    if (!ultraSafeMode_) {
        // Only handle disequalities at Full effort (model check).
        // At Standard effort (cb_propagate), partial assignments may not
        // give enough information for proveFixedValue, and split lemmas
        // cannot be propagated anyway (cb_propagate ignores lemmas).
        // This avoids useless work and prevents memory corruption bugs
        // triggered by repeated split-lemma generation in propagate.
        if (effort == TheoryEffort::Full && !disequalities_.empty()) {
            auto dr = handleDisequalities(lemmaDb);
            if (dr.kind != TheoryCheckResult::Kind::Consistent) {
#ifdef ZOLVER_LIA_PROFILE
                if (dr.kind == TheoryCheckResult::Kind::Lemma) {
                    profile_.disequalitySplitCount++;
                }
#endif
                return dr;
            }
        }
    }

    auto ir = ultraSafeMode_ ? TheoryCheckResult::consistent() : checkIntegrality(lemmaDb);

#ifdef ZOLVER_LIA_PROFILE
    auto prof_t5 = std::chrono::steady_clock::now();
    profile_.integralityCheckTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t5 - prof_t4).count();
    if (ir.kind == TheoryCheckResult::Kind::Lemma) {
        profile_.branchSplitCount++;
    }
#endif
    if (ir.kind == TheoryCheckResult::Kind::Consistent) {
        std::vector<DiseqValidationInfo> diseqInfos;
        for (const auto& d : disequalities_) {
            diseqInfos.push_back({d.auxVar});
        }
        if (!validator_.validateLiaModel(activeAtoms_, diseqInfos, integerVars_, gs_)) {
            dumpState("sat_validator_failed");
            return TheoryCheckResult::unknown();
        }
        dumpState("sat");
        return TheoryCheckResult::consistent();
    }

    if (!ultraSafeMode_ && !activeAtoms_.empty()) {
        auto cr = integerReasoner_.run(activeAtoms_);
        if (cr) {
            if (cr->kind == TheoryCheckResult::Kind::Lemma && cr->lemmaOpt) {
                if (!lemmaDb.contains(*cr->lemmaOpt)) return *cr;
            } else {
                return *cr;
            }
        }
    }

    if (ir.kind == TheoryCheckResult::Kind::Lemma && ir.lemmaOpt) {
        if (!lemmaDb.contains(*ir.lemmaOpt)) {
            return ir;
        }
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult LiaSolver::handleDisequalities(TheoryLemmaStorage& lemmaDb) {
    return handleSimplexDisequalities(
        disequalities_, gs_, lemmaDb,
        [this](const DiseqInfo& d) -> TheoryCheckResult {
            // If the disequality is forced to be false by current bounds
            // (auxVar is fixed to 0), return a precise conflict.
            auto val = gs_.value(d.auxVar);
            auto proved = gs_.proveFixedValue(d.auxVar);
            if (proved && proved->first.isZero()) {
                TheoryConflict tc;
                for (const auto& br : proved->second) {
                    tc.clause.push_back(br.reason);
                }
                tc.clause.push_back(d.lit);
                bool ok = normalizeTheoryClause(tc.clause);
                assert(ok && "complementary literal in disequality conflict");
                (void)ok;
                return TheoryCheckResult::mkConflict(std::move(tc));
            }

            if (d.rhs.get_den() != 1) {
                return TheoryCheckResult::consistent();
            }

            mpz_class g = 0;
            for (const auto& t : d.lhs.terms) {
                const mpq_class& c = t.second;
                if (c.get_den() != 1) {
                    g = 1;
                    break;
                }
                mpz_class a = c.get_num();
                if (a < 0) a = -a;
                if (a == 0) continue;
                if (g == 0) {
                    g = a;
                } else {
                    mpz_class tmp;
                    mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
                    g = tmp;
                }
            }

            mpz_class c = d.rhs.get_num();

            if (g == 0) {
                if (c == 0) {
                    auto tc = TheoryConflict{{d.lit}};
                    bool ok = normalizeTheoryClause(tc.clause);
                    assert(ok && "complementary literal in gcd conflict");
                    (void)ok;
                    return TheoryCheckResult::mkConflict(std::move(tc));
                }
                return TheoryCheckResult::consistent();
            }

            if (c % g != 0) {
                return TheoryCheckResult::consistent();
            }

            assert(registry_ != nullptr);
            mpq_class leRhs = mpq_class(c - g, 1);
            mpq_class geRhs = mpq_class(c + g, 1);

            auto lit1 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Leq, leRhs, TheoryId::LIA);
            auto lit2 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Geq, geRhs, TheoryId::LIA);

            return TheoryCheckResult::mkLemma(
                TheoryLemma{{d.lit.negated(), lit1, lit2}});
        });
}

TheoryCheckResult LiaSolver::checkIntegrality(TheoryLemmaStorage& /*lemmaDb*/) {
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int v : integerVars_) {
        auto val = gs_.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            mpq_class frac;
            if (val.b != 0) {
                // Delta-rational: value is a + b·δ where δ is infinitesimal.
                // If b > 0, value is just above a (frac ≈ 1).
                // If b < 0, value is just below a (frac ≈ 0).
                // Use 1/2 as a representative fractional distance.
                frac = mpq_class(1, 2);
            } else {
                // Compute fractional part = |val.a - floor(val.a)|
                mpz_class num = val.a.get_num();
                mpz_class den = val.a.get_den();
                mpz_class f = num / den;  // truncates toward zero
                mpz_class r = num % den;
                mpz_class floorVal;
                if (r == 0) {
                    floorVal = f;
                } else if (num >= 0) {
                    floorVal = f;
                } else {
                    floorVal = f - 1;
                }
                frac = val.a - mpq_class(floorVal, 1);
                if (frac < 0) frac = -frac;
            }
            if (frac > bestFrac) {
                bestFrac = frac;
                bestVar = v;
            }
        }
    }

    if (bestVar != -1) {
        assert(registry_ != nullptr);
        return TheoryCheckResult::mkLemma(buildBranchSplitLemma(bestVar, gs_.value(bestVar)));
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma LiaSolver::buildBranchSplitLemma(int var, const DeltaRational& val) {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        if (val.b > 0) {
            // value = a + epsilon, strictly greater than a
            floorVal = q;
            ceilVal = mpq_class(num + 1, 1);
        } else if (val.b < 0) {
            // value = a - epsilon, strictly less than a
            floorVal = mpq_class(num - 1, 1);
            ceilVal = q;
        } else {
            floorVal = q;
            ceilVal = q;
        }
    } else {
        mpz_class f = num / den;
        mpz_class r = num % den;
        if (r == 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f, 1);
        } else if (num >= 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f + 1, 1);
        } else {
            floorVal = mpq_class(f - 1, 1);
            ceilVal = mpq_class(f, 1);
        }
    }

    std::string name = manager_.getVarName(var);
    if (name.empty()) {
        return TheoryLemma{};
    }

    LinearFormKey form;
    form.terms.push_back({name, mpq_class(1)});

    auto litLo = registry_->getOrCreateLinearBoundAtom(form, Relation::Leq, floorVal, TheoryId::LIA);
    auto litHi = registry_->getOrCreateLinearBoundAtom(form, Relation::Geq, ceilVal, TheoryId::LIA);

    return TheoryLemma{{litLo, litHi}};
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (experimental skeleton for non-convex LIA)
// ---------------------------------------------------------------------------

std::string LiaSolver::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = coreIr_->get(st->coreExpr);
    std::string name;
    if (expr.kind == Kind::Variable) {
        if (std::holds_alternative<std::string>(expr.payload.value)) {
            name = std::get<std::string>(expr.payload.value);
        }
    } else if (expr.isConst()) {
        // Constants participate in interface equalities via a synthetic variable.
        // The actual constant value is enforced via bound assertion in check().
        name = "__const_" + st->name;
    }
    if (!name.empty()) {
        sharedTermToVarName_[s] = name;
    }
    return name;
}

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
    std::cerr << "[LIA-IEQ] add a=" << a << " b=" << b << " reason=" << (reason.sign?"+":"-") << "v" << reason.var
              << " level=" << level << " eqSize=" << interfaceEqualities_.size()
              << " diseqSize=" << interfaceDisequalities_.size() << "\n";
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    // Remove stale equality for the same pair
    auto it = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [a, b](const auto& e) { return e.a == a && e.b == b; });
    interfaceEqualities_.erase(it, interfaceEqualities_.end());

    interfaceDisequalities_.push_back({a, b, reason, level});
    // Invalidate simplex state because an interface disequality may remove a
    // previously-applied interface equality bound.  Force full rebuild on next check.
    gs_.resetActiveBounds();
    appliedCursor_ = 0;
    return TheoryCheckResult::consistent();
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
                // Care-graph prune (ZOLVER_COMB_CAREGRAPH): skip same-value
                // pairs no theory cares about. Sound (under-propagation cannot
                // cause wrong UNSAT).
                if (careGraph_ && !careGraph_->caresPair(terms[i].first, terms[j].first))
                    continue;
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
        for (size_t i = 0; i < sharedVars.size(); ++i) {
            for (size_t j = i + 1; j < sharedVars.size(); ++j) {
                // Care-graph prune (ZOLVER_COMB_CAREGRAPH): only propagate to
                // EUF for pairs some theory cares about. Sound: under-propagation
                // loses completeness (caught by ModelValidator), never UNSAT.
                if (careGraph_ && !careGraph_->caresPair(sharedVars[i], sharedVars[j]))
                    continue;
                auto reasons = assertedVarEqualityReason(sharedVars[i], sharedVars[j]);
                if (reasons.empty()) continue;
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    sharedVars[i], sharedVars[j], std::move(reasons)});
            }
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
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;
    DeltaRational val = gs_.value(idx);
    // Integer model values are integral after check(); the delta part is an
    // infinitesimal that does not affect the integer comparison.
    return RealValue::fromMpq(val.a);
}

std::optional<TheorySolver::TheoryModel> LiaSolver::getModel() const {
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;           // skip auxiliary vars
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue; // internal
        DeltaRational val = gs_.value(i);
        // For integer variables, value should be integral after check().
        // If delta component is non-zero, take the rational part (delta is infinitesimal).
        if (val.b == 0 && val.a.get_den() == 1) {
            model.assignments[name] = val.a.get_num().get_str();
        } else {
            model.assignments[name] = val.a.get_str();
        }
        model.numericAssignments.insert({name, RealValue::fromMpq(val.a)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

// ============================================================================
// Debug dump helpers
// ============================================================================

std::string LiaSolver::mpqToSmtLib(const mpq_class& q) {
    if (q.get_den() == 1) {
        return q.get_num().get_str();
    }
    return "(/ " + q.get_num().get_str() + " " + q.get_den().get_str() + ")";
}

std::string LiaSolver::relationToSmtLib(Relation rel) {
    switch (rel) {
        case Relation::Eq:  return "=";
        case Relation::Lt:  return "<";
        case Relation::Leq: return "<=";
        case Relation::Gt:  return ">";
        case Relation::Geq: return ">=";
        case Relation::Neq: return "distinct";
    }
    return "=";
}

std::string LiaSolver::linearFormToSmtLib(const LinearFormKey& form) {
    if (form.terms.empty()) return "0";
    if (form.terms.size() == 1) {
        const auto& [name, coeff] = form.terms[0];
        if (coeff == 1) return name;
        if (coeff == -1) return "(- " + name + ")";
        return "(* " + mpqToSmtLib(coeff) + " " + name + ")";
    }
    std::string s = "(+";
    for (const auto& [name, coeff] : form.terms) {
        if (coeff == 1) {
            s += " " + name;
        } else if (coeff == -1) {
            s += " (- " + name + ")";
        } else {
            s += " (* " + mpqToSmtLib(coeff) + " " + name + ")";
        }
    }
    s += ")";
    return s;
}

void LiaSolver::dumpState(const std::string& tag) const {
    const char* env = std::getenv("ZOLVER_LIA_DUMP_DIR");
    if (!env || !*env) return;
    std::filesystem::path dir(env);
    if (!std::filesystem::exists(dir)) {
        std::filesystem::create_directories(dir);
    }

    int id = ++dumpCounter_;
    std::filesystem::path path = dir / ("lia_dump_" + std::to_string(id) + "_" + tag + ".smt2");
    std::ofstream ofs(path);
    if (!ofs) return;

    ofs << "(set-logic QF_LIA)\n";

    // Collect all variable names
    std::unordered_set<std::string> vars;
    for (const auto& a : activeAtoms_) {
        for (const auto& t : a.lhs.terms) vars.insert(t.first);
    }
    for (const auto& d : disequalities_) {
        for (const auto& t : d.lhs.terms) vars.insert(t.first);
    }
    for (const auto& ie : interfaceEqualities_) {
        (void)ie;
    }

    for (const auto& v : vars) {
        ofs << "(declare-fun " << v << " () Int)\n";
    }

    // Active atoms
    for (const auto& a : activeAtoms_) {
        Relation effectiveRel = a.value ? a.rel : negateRelation(a.rel);
        std::string lhsStr = linearFormToSmtLib(a.lhs);
        std::string rhsStr = mpqToSmtLib(a.rhs);
        if (effectiveRel == Relation::Neq) {
            ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
        } else {
            ofs << "(assert (" << relationToSmtLib(effectiveRel) << " " << lhsStr << " " << rhsStr << "))\n";
        }
    }

    // Disequalities
    for (const auto& d : disequalities_) {
        std::string lhsStr = linearFormToSmtLib(d.lhs);
        std::string rhsStr = mpqToSmtLib(d.rhs);
        ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
    }

    ofs << "(check-sat)\n";

    if (tag == "sat") {
        ofs << "(get-model)\n";
    }

    ofs.flush();
}

std::optional<bool> LiaSolver::z3CheckCurrentState() const {
    const char* env = std::getenv("ZOLVER_LIA_Z3_CHECK");
    if (!env || !*env) return std::nullopt;

    std::filesystem::path tmpDir = std::filesystem::temp_directory_path();
    std::string base = "zolver_lia_z3check_" + std::to_string(getpid()) + "_" + std::to_string(dumpCounter_);
    std::filesystem::path smtPath = tmpDir / (base + ".smt2");
    std::filesystem::path outPath = tmpDir / (base + ".out");

    {
        std::ofstream ofs(smtPath);
        if (!ofs) return std::nullopt;

        ofs << "(set-logic QF_LIA)\n";
        std::unordered_set<std::string> vars;
        for (const auto& a : activeAtoms_) {
            for (const auto& t : a.lhs.terms) vars.insert(t.first);
        }
        for (const auto& d : disequalities_) {
            for (const auto& t : d.lhs.terms) vars.insert(t.first);
        }
        for (const auto& v : vars) {
            ofs << "(declare-fun " << v << " () Int)\n";
        }
        for (const auto& a : activeAtoms_) {
            Relation effectiveRel = a.value ? a.rel : negateRelation(a.rel);
            std::string lhsStr = linearFormToSmtLib(a.lhs);
            std::string rhsStr = mpqToSmtLib(a.rhs);
            if (effectiveRel == Relation::Neq) {
                ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
            } else {
                ofs << "(assert (" << relationToSmtLib(effectiveRel) << " " << lhsStr << " " << rhsStr << "))\n";
            }
        }
        for (const auto& d : disequalities_) {
            std::string lhsStr = linearFormToSmtLib(d.lhs);
            std::string rhsStr = mpqToSmtLib(d.rhs);
            ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
        }
        ofs << "(check-sat)\n";
    }

    std::string cmd = std::string("z3 -T:5 ") + smtPath.string() + " > " + outPath.string() + " 2>/dev/null";
    int ret = std::system(cmd.c_str());
    (void)ret;

    std::ifstream ifs(outPath);
    if (!ifs) {
        std::filesystem::remove(smtPath);
        std::filesystem::remove(outPath);
        return std::nullopt;
    }
    std::string line;
    bool isSat = false;
    while (std::getline(ifs, line)) {
        if (line.find("sat") != std::string::npos && line.find("unsat") == std::string::npos) {
            isSat = true;
        } else if (line.find("unsat") != std::string::npos) {
            isSat = false;
        }
    }

    std::filesystem::remove(smtPath);
    std::filesystem::remove(outPath);
    return isSat;
}

} // namespace zolver
