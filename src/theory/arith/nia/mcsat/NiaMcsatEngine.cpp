#include "theory/arith/nia/mcsat/NiaMcsatEngine.h"

#include "expr/ir.h"
#include "util/EnvParam.h"
#include "theory/arith/linear/LinearExpr.h"      // negateRelation
#include "theory/arith/nra/core/CdcacCommon.h"   // Sign, relationHolds (shared)
#include "theory/arith/poly/PolynomialKernel.h"

#include <algorithm>
#include <optional>
#include <unordered_map>

namespace xolver {
namespace nia_mcsat {

NiaMcsatEngine::NiaMcsatEngine() = default;
NiaMcsatEngine::~NiaMcsatEngine() = default;

void NiaMcsatEngine::reset() {
    asserted_.clear();
    varOrderCache_.clear();
    varOrderCacheValid_ = false;
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

void NiaMcsatEngine::onAssertAtom(const TheoryAtomRecord& atom, bool value,
                                  int level, SatLit assertedLit) {
    asserted_.push_back({atom, value, level, assertedLit});
    varOrderCacheValid_ = false;
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

void NiaMcsatEngine::onBacktrack(int targetLevel) {
    while (!asserted_.empty() && asserted_.back().level > targetLevel) {
        asserted_.pop_back();
    }
    varOrderCacheValid_ = false;
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

std::unordered_set<VarId> NiaMcsatEngine::collectVariables_() const {
    std::unordered_set<VarId> vars;
    if (!kernel_) return vars;
    for (const auto& a : asserted_) {
        if (auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload)) {
            auto names = kernel_->variables(pp->poly);
            for (const auto& n : names) {
                if (auto v = kernel_->findVar(n)) vars.insert(*v);
            }
        }
    }
    return vars;
}

VarId NiaMcsatEngine::pickNextVar(const mcsat::MCSatTrail& trail) {
    if (!varOrderCacheValid_) {
        auto vars = collectVariables_();
        varOrderCache_.assign(vars.begin(), vars.end());
        std::sort(varOrderCache_.begin(), varOrderCache_.end());
        varOrderCacheValid_ = true;
    }
    for (VarId v : varOrderCache_) {
        if (!trail.lookupVar(v)) return v;
    }
    return NullVar;
}

namespace {

// Pull an exact integer out of a RealValue; nullopt if the value is not
// an exact integer (a rational p/q with q != 1, or an algebraic). NIA
// values are integers by definition — a non-integer trail value here is
// an invariant violation (or an algebraic backend) and we bail out via
// GiveUp at the call site.
std::optional<mpz_class> intOfRealValue(const RealValue& rv) {
    if (!rv.isExactInteger()) return std::nullopt;
    auto q = rv.tryAsRational();
    if (!q) return std::nullopt;
    return q->get_num();
}

// Build an integer sample from the trail; optionally extend with
// (extraVar → extraValue). Returns nullopt if any trail entry's value is
// not an exact integer.
std::optional<std::unordered_map<VarId, mpz_class>>
buildIntSample(const mcsat::MCSatTrail& trail,
               VarId extraVar,
               const mpz_class* extraValue) {
    std::unordered_map<VarId, mpz_class> sample;
    for (const auto& e : trail.entries()) {
        if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
            e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
        auto z = intOfRealValue(e.value);
        if (!z) return std::nullopt;
        sample[e.var] = std::move(*z);
    }
    if (extraVar != NullVar && extraValue) {
        sample[extraVar] = *extraValue;
    }
    return sample;
}

// Translate the integer sample into the rational sample sgnVarId wants.
std::unordered_map<VarId, mpq_class>
toRationalSample(const std::unordered_map<VarId, mpz_class>& z) {
    std::unordered_map<VarId, mpq_class> q;
    q.reserve(z.size());
    for (const auto& [v, val] : z) {
        q.emplace(v, mpq_class(val));
    }
    return q;
}

bool sampleCoversAllInt(const std::vector<std::string>& polyVars,
                        const std::unordered_map<VarId, mpz_class>& sample,
                        PolynomialKernel& kernel) {
    for (const auto& name : polyVars) {
        auto vid = kernel.findVar(name);
        if (!vid) return false;
        if (!sample.count(*vid)) return false;
    }
    return true;
}

bool atomHoldsForSign(Sign s, Relation rel, bool assertedValue) {
    Relation eff = assertedValue ? rel : negateRelation(rel);
    return relationHolds(s, eff);
}

Sign signFromInt(int sgn) {
    if (sgn < 0) return Sign::Neg;
    if (sgn > 0) return Sign::Pos;
    return Sign::Zero;
}

PolyId polyMinusRhs(PolynomialKernel& kernel, PolyId poly,
                    const mpq_class& rhs) {
    if (rhs == 0) return poly;
    return kernel.sub(poly, kernel.mkConst(rhs));
}

} // namespace

namespace {

// NIA DFS — mirrors NlsatEngine's complete-assignment search but
// integer-only. Default 50000; tunable via env for autotuning.
static const int NIA_DFS_NODE_BUDGET =
    env::paramInt("XOLVER_NIA_MCSAT_DFS_BUDGET", 50000);

bool niaFullSampleSatisfiesAtoms(
    PolynomialKernel& kernel,
    const std::vector<AssertedAtom>& atoms,
    const std::unordered_map<VarId, mpz_class>& sample) {
    auto qSample = toRationalSample(sample);
    for (const auto& a : atoms) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        if (!pp->rhs.isExactInteger()) return false;
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) return false;
        auto polyVars = kernel.variables(pp->poly);
        if (!sampleCoversAllInt(polyVars, sample, kernel)) continue;  // unbound → not yet evaluable
        PolyId effective = polyMinusRhs(kernel, pp->poly, *rhsQ);
        int sgnInt = kernel.sgnVarId(effective, qSample);
        Sign s = signFromInt(sgnInt);
        if (!atomHoldsForSign(s, pp->rel, a.value)) return false;
    }
    return true;
}

bool niaDfsAssign(PolynomialKernel& kernel,
                  const std::vector<AssertedAtom>& atoms,
                  const std::vector<mpz_class>& baseCands,
                  std::unordered_map<VarId, mpz_class>& sample,
                  const std::vector<VarId>& remaining,
                  size_t idx,
                  int& budget) {
    if (budget-- <= 0) return false;
    if (idx >= remaining.size()) {
        return niaFullSampleSatisfiesAtoms(kernel, atoms, sample);
    }
    VarId v = remaining[idx];
    for (const auto& cand : baseCands) {
        if (budget <= 0) return false;
        sample[v] = cand;
        if (niaFullSampleSatisfiesAtoms(kernel, atoms, sample)) {
            if (niaDfsAssign(kernel, atoms, baseCands, sample,
                             remaining, idx + 1, budget)) {
                return true;
            }
        }
        sample.erase(v);
    }
    return false;
}

} // namespace

mcsat::ValueChoice NiaMcsatEngine::pickValue(VarId var,
                                             const mcsat::MCSatTrail& trail) {
    if (!kernel_) {
        return mcsat::ValueChoice::giveUp("NiaMcsatEngine: no kernel");
    }

    // Cache lookup.
    if (cachedAssignmentSucceeded_) {
        auto it = cachedAssignment_.find(var);
        if (it != cachedAssignment_.end()) {
            return mcsat::ValueChoice::found(it->second);
        }
    }

    static const std::vector<mpz_class> BASE_CANDIDATES = {
        mpz_class(0),
        mpz_class(1), mpz_class(-1),
        mpz_class(2), mpz_class(-2),
        mpz_class(3), mpz_class(-3),
        mpz_class(4), mpz_class(-4),
        mpz_class(5), mpz_class(-5),
        mpz_class(10), mpz_class(-10),
    };

    // Run integer DFS over the full undecided set on the first pickValue.
    if (!cachedAssignmentTried_) {
        cachedAssignmentTried_ = true;

        std::unordered_map<VarId, mpz_class> sample;
        bool trailOk = true;
        for (const auto& e : trail.entries()) {
            if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
                e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
            auto z = intOfRealValue(e.value);
            if (!z) { trailOk = false; break; }
            sample[e.var] = *z;
        }
        if (!trailOk) {
            return mcsat::ValueChoice::giveUp(
                "NiaMcsatEngine: non-integer value on trail");
        }
        auto vars = collectVariables_();
        std::vector<VarId> remaining;
        for (VarId v : vars) {
            if (!sample.count(v)) remaining.push_back(v);
        }
        std::sort(remaining.begin(), remaining.end());
        auto it = std::find(remaining.begin(), remaining.end(), var);
        if (it != remaining.end()) {
            std::iter_swap(remaining.begin(), it);
        }

        int budget = NIA_DFS_NODE_BUDGET;
        if (niaDfsAssign(*kernel_, asserted_, BASE_CANDIDATES, sample,
                         remaining, 0, budget)) {
            cachedAssignmentSucceeded_ = true;
            for (const auto& [v, z] : sample) {
                cachedAssignment_[v] = RealValue::fromMpz(z);
            }
            auto cit = cachedAssignment_.find(var);
            if (cit != cachedAssignment_.end()) {
                return mcsat::ValueChoice::found(cit->second);
            }
        }
    }
    return mcsat::ValueChoice::giveUp(
        "NiaMcsatEngine: no integer candidate survived the asserted atoms");
}

std::vector<SatLit> NiaMcsatEngine::explainConflict(
    const mcsat::MCSatTrail& trail,
    const std::vector<TheoryAtomRecord>& blockingAtoms) {
    (void)trail;
    (void)blockingAtoms;
    // Empty → framework downgrades to Unknown (sound floor; §15.6).
    return {};
}

bool NiaMcsatEngine::validateModel(const mcsat::MCSatTrail& trail,
                                   TheorySolver::TheoryModel& outModel) {
    if (!kernel_) return false;
    auto sample = buildIntSample(trail, NullVar, nullptr);
    if (!sample) return false;
    auto qSample = toRationalSample(*sample);
    for (const auto& a : asserted_) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        if (!pp->rhs.isExactInteger()) return false;
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) return false;
        auto polyVars = kernel_->variables(pp->poly);
        if (!sampleCoversAllInt(polyVars, *sample, *kernel_)) {
            // Partial assignment → not a complete model.
            return false;
        }
        PolyId effective = polyMinusRhs(*kernel_, pp->poly, *rhsQ);
        int sgnInt = kernel_->sgnVarId(effective, qSample);
        Sign s = signFromInt(sgnInt);
        if (!atomHoldsForSign(s, pp->rel, a.value)) return false;
    }
    // Populate model channel — every theory entry becomes an
    // assignment, keyed by the kernel-resolved variable name.
    for (const auto& e : trail.entries()) {
        if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
            e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
        std::string name(kernel_->varName(e.var));
        outModel.numericAssignments[name] = e.value;
    }
    return true;
}

} // namespace nia_mcsat
} // namespace xolver
