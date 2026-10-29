#include "base/RuntimeConfig.h"
#include "applications/smt/common/lia/LiaSolver.h"
#include "base/MpqUtils.h"
#include "base/EnvParam.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "contracts/TheoryAtomTypes.h"
#include "search/arith/Reasoner.h"
#include "search/linear/SimplexDiseqSplitter.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/lia/GomoryCut.h"
#include "applications/smt/common/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

std::optional<bool> LiaSolver::evalAtomAtModel(SatVar variable) {
    const auto* record = registry_ ? registry_->findBySatVar(variable) : nullptr;
    if (!record) return std::nullopt;
    const auto* atom = std::get_if<LinearAtomPayload>(&record->payload);
    return atom ? manager_.evaluateAtModel(gs_, *atom) : std::nullopt;
}

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
    const auto revision = gs_.analysisRevision();
    const auto recordCount = registry_->records().size();
    if (revision && pinScanRevision_ == revision && pinScanRecords_ == recordCount) return;
    // Throttle: hard cap per check to avoid quadratic worst-case in the SAT bus.
    const size_t kMaxPropsPerScan = 256;
    size_t emitted = 0;
    bool completed = true;
    // Reuse the simplex snapshot across unchanged drains. Check the value and
    // emitted polarity before materializing a target's premise DAG.
    std::shared_ptr<const GeneralSimplex::FixedValueAnalysis> fixedAnalysis;
    auto fixedValue = [&](int idx) {
        if (!fixedAnalysis) fixedAnalysis = gs_.sharedFixedValueAnalysis();
        return fixedAnalysis->fixedValue(idx);
    };
    using FixedResult = decltype(gs_.proveFixedValue(0));
    std::unordered_map<int, FixedResult> fixedCache;
    auto cachedProveFixedValue = [&](int idx) -> const FixedResult& {
        auto it = fixedCache.find(idx);
        if (it != fixedCache.end()) return it->second;
        if (!fixedAnalysis) fixedAnalysis = gs_.sharedFixedValueAnalysis();
        return fixedCache.emplace(idx, fixedAnalysis->prove(idx)).first->second;
    };
    for (const auto& rec : registry_->records()) {
        if (emitted >= kMaxPropsPerScan) { completed = false; break; }
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
            struct SharedPin { mpq_class value; int var; };
            auto pinOf = [&](SharedTermId stId) -> std::optional<SharedPin> {
                if (sharedTermRegistry_->get(stId)) {
                    // Numeric-constant shared term has its value baked in.
                    if (auto cv = sharedTermRegistry_->constValue(stId)) {
                        return SharedPin{*cv, -1};
                    }
                }
                std::string nm = getVarNameForSharedTerm(stId);
                if (nm.empty()) return std::nullopt;
                int idx = manager_.findVarIndex(nm);
                if (idx < 0) return std::nullopt;
                const auto fv = fixedValue(idx);
                if (!fv) return std::nullopt;
                if (fv->b != 0) return std::nullopt;
                return SharedPin{fv->a, idx};
            };
            auto pa = pinOf(sp.a);
            auto pb = pinOf(sp.b);
            if (!pa || !pb) continue;
            bool atomTrue = (pa->value == pb->value);
            SatLit atomLit{rec.satVar, true};
            uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) | (atomTrue ? 1u : 0u);
            if (entailmentEmittedKeys_.contains(key)) continue;
            TheoryLemma lemma;
            auto appendReasons = [&](const SharedPin& pin) {
                if (pin.var < 0) return true;
                const auto& proof = cachedProveFixedValue(pin.var);
                if (!proof) return false;
                for (const auto& br : proof->second) lemma.lits.push_back(br.reason.negated());
                return true;
            };
            if (!appendReasons(*pa) || !appendReasons(*pb)) continue;
            entailmentEmittedKeys_.insert(key);
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

        if (p.rel != Relation::Eq) continue;            // limit to equality atoms
        if (p.lhs.terms.size() != 1) continue;          // single-var atom only
        const auto& [name, coeff] = p.lhs.terms[0];
        if (coeff == 0) continue;
        int idx = manager_.findVarIndex(name);
        if (idx < 0) continue;                          // not in simplex yet
        const auto value = fixedValue(idx);
        if (!value) continue;                           // not pinned by current bounds
        const DeltaRational& pinned = *value;
        if (pinned.b != 0) continue;                    // skip δ-strict (open) values
        // Atom `coeff*v = rhs` is true iff coeff * pinned.a == rhs.
        mpq_class lhsVal = coeff * pinned.a;
        bool atomTrue = (lhsVal == rhsVal);
        // Already assigned? Skip (TheoryManager will already see it).
        SatLit atomLit{rec.satVar, true};
        // Dedup: (satVar, polarity-as-int) → emitted once per backtrack epoch.
        uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) |
                       (atomTrue ? 1u : 0u);
        if (entailmentEmittedKeys_.contains(key)) continue;
        const auto& fixedOpt = cachedProveFixedValue(idx);
        if (!fixedOpt) continue;
        entailmentEmittedKeys_.insert(key);
        TheoryLemma lemma;
        for (const auto& br : fixedOpt->second) {
            lemma.lits.push_back(br.reason.negated());  // ~reasons
        }
        lemma.lits.push_back(atomTrue ? atomLit : atomLit.negated());
        entailmentProps_.push_back(std::move(lemma));
        ++emitted;
    }
    if (completed) {
        pinScanRevision_ = revision;
        pinScanRecords_ = recordCount;
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
