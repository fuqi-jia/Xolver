#include "util/MpqUtils.h"
#include "theory/arith/logics/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/kernel/linear/SimplexDiseqSplitter.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/arith/logics/lia/GomoryCut.h"
#include "theory/arith/logics/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include "theory/arith/logics/nia/reasoners/DioReasoner.h"
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

// Scan registered LIA atoms and emit entailment lemmas for unassigned ones
// whose value is FORCED by the current bounds. Covers the precise Wisa-class
// pattern: `(= v c)` linear-atom where v has been pinned by N-O propagation
// from EUF (e.g. bridge_J_i ~ bridge_K, bridge_K = 4 → bridge_J_i = 4). The
// gateway is single-variable equality atoms; multi-var entailment is left to
// the existing Farkas/getDeducedSharedEqualities pipeline. Sound: only emits
// atom-tightening lemmas whose reasons (the pinning literals) are currently
// asserted true, so `reasons → atom` is a tautology under the active trail.
void LiaSolver::scanLiteralPinEntailments() {
    if (!registry_) return;
    // Throttle: hard cap per check to avoid quadratic worst-case in the SAT bus.
    const size_t kMaxPropsPerScan = 256;
    size_t emitted = 0;
    // #87: memoize proveFixedValue across this scan. The scan iterates ALL atoms and
    // queries proveFixedValue for the SAME shared vars (sp.a/sp.b, LHS vars) across
    // many atoms — redundant recursion (the xs-13-09 Wisa cliff: 86% of samples in
    // GeneralSimplex::proveFixedValueImpl). The scan only READS the simplex
    // (proveFixedValue is const; no assert/pivot here), so the bounds+tableau are
    // STABLE throughout — caching by var index is sound + verdict-identical (same
    // result, computed once per var instead of once per occurrence). Local to this
    // call and discarded after, so there is no cross-mutation staleness.
    using FixedResult = decltype(gs_.proveFixedValue(0));
    std::unordered_map<int, FixedResult> fixedCache;
    auto cachedProveFixedValue = [&](int idx) -> const FixedResult& {
        auto it = fixedCache.find(idx);
        if (it != fixedCache.end()) return it->second;
        return fixedCache.emplace(idx, gs_.proveFixedValue(idx)).first->second;
    };
    for (const auto& rec : registry_->records()) {
        if (emitted >= kMaxPropsPerScan) break;
        // --- Path A: shared-equality atom (Combination): both sides are
        // SharedTerms; if BOTH currently pinned by LIA bounds, the atom value
        // is forced regardless of which theory owns the registration. This is
        // the path the Wisa-class goal atom `(= 4 bridge_J)` takes (both 4
        // and bridge_J are shared terms registered by Purifier::registerEufVars
        // and Purifier::makeFreshVar respectively). Without this branch the
        // goal atom escapes propagation and SAT settles on a sat model the
        // ArithModelValidator catches as violating (not (and L_1..L_6)) →
        // floor → unknown.
        if (rec.theory == TheoryId::Combination &&
            std::holds_alternative<SharedEqualityPayload>(rec.payload)) {
            const auto& sp = std::get<SharedEqualityPayload>(rec.payload);
            if (!sharedTermRegistry_) continue;
            auto pinOf = [&](SharedTermId stId) -> std::optional<std::pair<mpq_class, std::vector<SatLit>>> {
                if (sharedTermRegistry_->get(stId)) {
                    // Numeric-constant shared term has its value baked in.
                    if (auto cv = sharedTermRegistry_->constValue(stId)) {
                        return std::make_pair(*cv, std::vector<SatLit>{});
                    }
                }
                std::string nm = getVarNameForSharedTerm(stId);
                if (nm.empty()) return std::nullopt;
                int idx = manager_.findVarIndex(nm);
                if (idx < 0) return std::nullopt;
                const auto& fv = cachedProveFixedValue(idx);
                if (!fv) return std::nullopt;
                if (fv->first.b != 0) return std::nullopt;
                std::vector<SatLit> reasons;
                reasons.reserve(fv->second.size());
                for (const auto& br : fv->second) reasons.push_back(br.reason);
                return std::make_pair(fv->first.a, std::move(reasons));
            };
            auto pa = pinOf(sp.a);
            auto pb = pinOf(sp.b);
            if (!pa || !pb) continue;
            bool atomTrue = (pa->first == pb->first);
            SatLit atomLit{rec.satVar, true};
            uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) | (atomTrue ? 1u : 0u);
            if (!entailmentEmittedKeys_.insert(key).second) continue;
            TheoryLemma lemma;
            for (const auto& r : pa->second) lemma.lits.push_back(r.negated());
            for (const auto& r : pb->second) lemma.lits.push_back(r.negated());
            lemma.lits.push_back(atomTrue ? atomLit : atomLit.negated());
            entailmentProps_.push_back(std::move(lemma));
            ++emitted;
            continue;
        }
        if (rec.theory != TheoryId::LIA) continue;
        if (!std::holds_alternative<LinearAtomPayload>(rec.payload)) continue;
        const auto& p = std::get<LinearAtomPayload>(rec.payload);
        if (!p.rhs.isRational()) continue;
        const mpq_class& rhsVal = p.rhs.asRational();

        // XOLVER_LIA_ENTAIL_GEN (default-OFF): generalize entailment beyond the
        // single-variable equality gateway to ANY LIA atom (any relation, any
        // arity) whose entire LHS is currently PINNED to a constant by the
        // simplex bounds. This is z3's `arith-fixed-eqs` channel — the one the
        // cs_* QF_ANIA traces need (their atoms are 2-var equalities `(= a b)`
        // and bound-pairs `(<= a b)`, all skipped by the single-var path). Sound:
        // if every var in the LHS is fixed (lb==ub, δ=0) the atom's truth is
        // determined, and the lemma (¬fixing-bounds ∨ atom) is theory-valid — the
        // same proveFixedValue bound-reason mechanism the single-var path below
        // already trusts in combination.
        static const bool genEntail =
            xolver::env::diag("XOLVER_LIA_ENTAIL_GEN");
        if (genEntail) {
            if (p.rel != Relation::Eq && p.rel != Relation::Leq &&
                p.rel != Relation::Geq && p.rel != Relation::Lt &&
                p.rel != Relation::Gt) continue;
            if (p.lhs.terms.empty()) continue;
            mpq_class lhsVal = 0;
            std::vector<SatLit> reasons;
            bool allPinned = true;
            for (const auto& [name, coeff] : p.lhs.terms) {
                if (coeff == 0) continue;
                int idx = manager_.findVarIndex(name);
                if (idx < 0) { allPinned = false; break; }
                const auto& fv = cachedProveFixedValue(idx);
                if (!fv || fv->first.b != 0) { allPinned = false; break; }
                lhsVal += coeff * fv->first.a;
                for (const auto& br : fv->second) reasons.push_back(br.reason);
            }
            if (!allPinned) continue;
            bool atomTrue;
            switch (p.rel) {
                case Relation::Eq:  atomTrue = (lhsVal == rhsVal); break;
                case Relation::Leq: atomTrue = (lhsVal <= rhsVal); break;
                case Relation::Geq: atomTrue = (lhsVal >= rhsVal); break;
                case Relation::Lt:  atomTrue = (lhsVal <  rhsVal); break;
                case Relation::Gt:  atomTrue = (lhsVal >  rhsVal); break;
                default: continue;
            }
            SatLit atomLit{rec.satVar, true};
            uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) | (atomTrue ? 1u : 0u);
            if (!entailmentEmittedKeys_.insert(key).second) continue;
            TheoryLemma lemma;
            for (const auto& r : reasons) lemma.lits.push_back(r.negated());
            lemma.lits.push_back(atomTrue ? atomLit : atomLit.negated());
            entailmentProps_.push_back(std::move(lemma));
            ++emitted;
            continue;
        }

        // Default single-variable equality gateway (unchanged).
        if (p.rel != Relation::Eq) continue;            // limit to equality atoms
        if (p.lhs.terms.size() != 1) continue;          // single-var atom only
        const auto& [name, coeff] = p.lhs.terms[0];
        if (coeff == 0) continue;
        int idx = manager_.findVarIndex(name);
        if (idx < 0) continue;                          // not in simplex yet
        const auto& fixedOpt = cachedProveFixedValue(idx);
        if (!fixedOpt) continue;                        // not pinned by current bounds
        const DeltaRational& pinned = fixedOpt->first;
        if (pinned.b != 0) continue;                    // skip δ-strict (open) values
        // Atom `coeff*v = rhs` is true iff coeff * pinned.a == rhs.
        mpq_class lhsVal = coeff * pinned.a;
        bool atomTrue = (lhsVal == rhsVal);
        // Already assigned? Skip (TheoryManager will already see it).
        SatLit atomLit{rec.satVar, true};
        // Dedup: (satVar, polarity-as-int) → emitted once per backtrack epoch.
        uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) |
                       (atomTrue ? 1u : 0u);
        if (!entailmentEmittedKeys_.insert(key).second) continue;
        TheoryLemma lemma;
        for (const auto& br : fixedOpt->second) {
            lemma.lits.push_back(br.reason.negated());  // ~reasons
        }
        lemma.lits.push_back(atomTrue ? atomLit : atomLit.negated());
        entailmentProps_.push_back(std::move(lemma));
        ++emitted;
    }
}

std::vector<TheoryLemma> LiaSolver::takeEntailmentPropagations() {
    // Lazy: refresh on every drain since the bounds may have moved since the
    // last check(). The scanner is bounded and idempotent (dedup).
    scanLiteralPinEntailments();
    return std::move(entailmentProps_);
}

std::optional<std::pair<mpq_class, std::vector<SatLit>>>
LiaSolver::proveFixedValueByName(const std::string& name) const {
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;          // var not in the simplex
    auto fv = gs_.proveFixedValue(idx);
    if (!fv) return std::nullopt;              // not pinned by current bounds
    if (fv->first.b != 0) return std::nullopt; // δ-strict (open) value — skip
    std::vector<SatLit> reasons;
    reasons.reserve(fv->second.size());
    for (const auto& br : fv->second) reasons.push_back(br.reason);
    return std::make_pair(fv->first.a, std::move(reasons));
}

std::optional<std::pair<mpq_class, std::vector<SatLit>>>
LiaSolver::proveFixedFormValue(const LinearFormKey& lhs, const mpq_class& rhs) {
    if (lhs.terms.empty()) return std::nullopt;       // constant form — nothing to pin
    // Sign-canonicalize so this query hits the SAME aux as canonically-fed
    // constraints (complementary forms share one aux). If negated, the canonical
    // aux value is the negation of (lhs - rhs), so flip the returned value back.
    LinearFormKey cLhs = lhs;
    mpq_class cRhs = rhs;
    Relation dummy = Relation::Eq;
    bool flipped = LinearConstraintNormalizer::canonicalizeSign(cLhs, dummy, cRhs);
    int aux = manager_.getOrCreateAuxVar(gs_, cLhs, cRhs);  // aux = cLhs - cRhs
    auto fv = gs_.proveFixedValue(aux);
    if (!fv) return std::nullopt;
    if (fv->first.b != 0) return std::nullopt;        // δ-strict (open) value
    mpq_class val = flipped ? -fv->first.a : fv->first.a;  // un-flip to (lhs - rhs)
    std::vector<SatLit> reasons;
    reasons.reserve(fv->second.size());
    for (const auto& br : fv->second) reasons.push_back(br.reason);
    return std::make_pair(val, std::move(reasons));
}

void LiaSolver::clearEntailmentDedupForBacktrack(int level) {
    // Reset the dedup at level 0 (full restart of the SAT decision chain).
    // We keep it across non-root backtracks: an entailment proven at a deeper
    // level under literals that are still asserted now stays sound to re-emit
    // (SAT will simply ignore the duplicate), but the cost of needless
    // re-emission is small and the buffer guards against churn.
    if (level == 0) {
        entailmentEmittedKeys_.clear();
        entailmentProps_.clear();
    }
}

} // namespace xolver
