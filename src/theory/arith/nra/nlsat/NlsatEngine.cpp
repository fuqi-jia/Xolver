#include "theory/arith/nra/nlsat/NlsatEngine.h"

#include "expr/ir.h"
#include "theory/arith/linear/LinearExpr.h"      // negateRelation
#include "theory/arith/nra/backend/AlgebraBackend.h"
#include "theory/arith/nra/core/CdcacCommon.h"   // Sign, relationHolds
#include "theory/arith/nra/core/CdcacConstraint.h" // CdcacInput
#include "theory/arith/nra/core/CdcacCore.h"     // mgc-H fallback
#include "theory/arith/nra/core/CdcacResult.h"   // CdcacResult
#include "theory/arith/poly/PolynomialKernel.h"

#include <algorithm>
#include <optional>
#include <unordered_map>

namespace xolver {
namespace nlsat {

NlsatEngine::NlsatEngine() = default;
NlsatEngine::~NlsatEngine() = default;

void NlsatEngine::setAlgebra(PolynomialKernel* kernel, AlgebraBackend* backend) {
    kernel_ = kernel;
    algebra_ = backend;
}

void NlsatEngine::reset() {
    asserted_.clear();
    varOrderCache_.clear();
    varOrderCacheValid_ = false;
    pendingExplainClause_.clear();
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

void NlsatEngine::onAssertAtom(const TheoryAtomRecord& atom, bool value,
                               int level, SatLit assertedLit) {
    asserted_.push_back({atom, value, level, assertedLit});
    varOrderCacheValid_ = false;
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

void NlsatEngine::onBacktrack(int targetLevel) {
    while (!asserted_.empty() && asserted_.back().level > targetLevel) {
        asserted_.pop_back();
    }
    varOrderCacheValid_ = false;
    pendingExplainClause_.clear();
    cachedAssignment_.clear();
    cachedAssignmentTried_ = false;
    cachedAssignmentSucceeded_ = false;
}

std::unordered_set<VarId> NlsatEngine::collectVariables_() const {
    std::unordered_set<VarId> vars;
    if (!kernel_) return vars;
    for (const auto& a : asserted_) {
        if (auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload)) {
            auto names = kernel_->variables(pp->poly);
            for (const auto& n : names) {
                if (auto v = kernel_->findVar(n)) {
                    vars.insert(*v);
                }
            }
        }
    }
    return vars;
}

namespace {

// Score variables by constraint-simplicity for variable ordering.
// LOWER score = process EARLIER. The intuition follows NLSAT's
// "easy-first" pattern: vars constrained by single-variable atoms
// (e.g. `v > 0`, `v = c`) are nearly free choices, so picking them
// first reduces the branching factor for the rest of the trail.
//
// Score components (smaller is earlier):
//   - 0 if the var has a single-variable equality atom (forced value)
//   - 1 if it has a single-variable inequality (e.g. positivity)
//   - 1000 + atomCount otherwise
struct VarScore {
    VarId v;
    int score;
};

int scoreVariable(PolynomialKernel& kernel,
                  const std::vector<AssertedAtom>& atoms,
                  VarId v) {
    int singleVarEq = 0;
    int singleVarIneq = 0;
    int atomCount = 0;
    std::string name(kernel.varName(v));
    for (const auto& a : atoms) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        auto vars = kernel.variables(pp->poly);
        bool containsV = false;
        bool onlyV = true;
        for (const auto& n : vars) {
            if (n == name) { containsV = true; continue; }
            onlyV = false;
        }
        if (!containsV) continue;
        ++atomCount;
        if (onlyV) {
            Relation eff = a.value ? pp->rel : Relation::Eq; // approx — flipped Eq stays Eq
            if (eff == Relation::Eq) ++singleVarEq;
            else ++singleVarIneq;
        }
    }
    if (singleVarEq > 0) return 0;          // forced — pick first
    if (singleVarIneq > 0) return 1;         // bounded — pick early
    return 1000 + atomCount;                  // unconstrained — pick later
}

} // namespace

VarId NlsatEngine::pickNextVar(const mcsat::MCSatTrail& trail) {
    if (!varOrderCacheValid_) {
        auto vars = collectVariables_();
        // mgc-A: replace VarId-sorted order with a constraint-simplicity
        // score so the easy vars (single-var positivity / equality)
        // are picked FIRST. Reduces the DFS branching factor on
        // structured benchmarks like Sturm-MGC.
        std::vector<VarScore> scored;
        scored.reserve(vars.size());
        for (VarId v : vars) {
            scored.push_back({v, scoreVariable(*kernel_, asserted_, v)});
        }
        std::sort(scored.begin(), scored.end(),
                  [](const VarScore& a, const VarScore& b) {
                      if (a.score != b.score) return a.score < b.score;
                      return a.v < b.v;  // tie-break by VarId for determinism
                  });
        varOrderCache_.clear();
        varOrderCache_.reserve(scored.size());
        for (const auto& s : scored) varOrderCache_.push_back(s.v);
        varOrderCacheValid_ = true;
    }
    for (VarId v : varOrderCache_) {
        if (!trail.lookupVar(v)) return v;
    }
    return NullVar;
}

namespace {

std::optional<std::unordered_map<VarId, mpq_class>>
buildSample(const mcsat::MCSatTrail& trail,
            VarId extraVar,
            const mpq_class* extraValue) {
    std::unordered_map<VarId, mpq_class> sample;
    for (const auto& e : trail.entries()) {
        if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
            e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
        auto q = e.value.tryAsRational();
        if (!q) return std::nullopt;
        sample[e.var] = *q;
    }
    if (extraVar != NullVar && extraValue) {
        sample[extraVar] = *extraValue;
    }
    return sample;
}

bool sampleCoversAll(const std::vector<std::string>& polyVars,
                     const std::unordered_map<VarId, mpq_class>& sample,
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

PolyId polyMinusRhs(PolynomialKernel& kernel,
                    PolyId poly,
                    const mpq_class& rhs) {
    if (rhs == 0) return poly;
    return kernel.sub(poly, kernel.mkConst(rhs));
}

// Dividing both sides by a negative coefficient flips the relation.
Relation flipRelation(Relation r) {
    switch (r) {
        case Relation::Eq:  return Relation::Eq;
        case Relation::Neq: return Relation::Neq;
        case Relation::Lt:  return Relation::Gt;
        case Relation::Leq: return Relation::Geq;
        case Relation::Gt:  return Relation::Lt;
        case Relation::Geq: return Relation::Leq;
    }
    return r;
}

// A single linear-bound derived from a "simple" asserted atom on v.
// Recognized atoms have poly = a*v + b (no other variables, degree 1)
// with an integer (a, b) and a rational rhs c, yielding `v rel'  (c-b)/a`
// where rel' is rel or its flip depending on the sign of a.
struct LinearBound {
    enum class Kind { Lower, Upper, Equal } kind;
    mpq_class value;
    bool open = false;     // strict (<, >) → open; non-strict (=, ≤, ≥) → closed
    SatLit reason;
};

std::optional<LinearBound> detectSimpleBound(
    PolynomialKernel& kernel,
    const AssertedAtom& a,
    VarId v) {
    auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
    if (!pp) return std::nullopt;
    auto vars = kernel.variables(pp->poly);
    if (vars.size() != 1) return std::nullopt;
    auto vid = kernel.findVar(vars[0]);
    if (!vid || *vid != v) return std::nullopt;

    // getIntegerCoefficients returns coefficients in DESCENDING degree
    // (e.g. [a, b] for a*v + b). We only handle linear in v.
    auto coefs = kernel.getIntegerCoefficients(pp->poly, vars[0]);
    if (!coefs || coefs->size() != 2) return std::nullopt;
    mpz_class a_z = (*coefs)[0];
    mpz_class b_z = (*coefs)[1];
    if (a_z == 0) return std::nullopt;  // degenerate

    auto rhsQ = pp->rhs.tryAsRational();
    if (!rhsQ) return std::nullopt;

    mpq_class boundValue = (*rhsQ - mpq_class(b_z)) / mpq_class(a_z);

    Relation rel = a.value ? pp->rel : negateRelation(pp->rel);
    if (a_z < 0) rel = flipRelation(rel);

    LinearBound lb;
    lb.value = boundValue;
    lb.reason = a.assertedLit;
    switch (rel) {
        case Relation::Eq:  lb.kind = LinearBound::Kind::Equal; lb.open = false; break;
        case Relation::Neq: return std::nullopt;  // disequality complicates intervals
        case Relation::Lt:  lb.kind = LinearBound::Kind::Upper; lb.open = true;  break;
        case Relation::Leq: lb.kind = LinearBound::Kind::Upper; lb.open = false; break;
        case Relation::Gt:  lb.kind = LinearBound::Kind::Lower; lb.open = true;  break;
        case Relation::Geq: lb.kind = LinearBound::Kind::Lower; lb.open = false; break;
    }
    return lb;
}

struct AccumulatedInterval {
    bool hasLo = false;
    mpq_class lo;
    bool loOpen = false;
    SatLit loReason{};
    bool hasHi = false;
    mpq_class hi;
    bool hiOpen = false;
    SatLit hiReason{};
    bool emptied = false;
    std::vector<SatLit> emptyReasons;
};

void mergeLowerBound(AccumulatedInterval& iv,
                     const mpq_class& v, bool open, SatLit reason) {
    if (!iv.hasLo) {
        iv.hasLo = true; iv.lo = v; iv.loOpen = open; iv.loReason = reason;
        return;
    }
    if (v > iv.lo || (v == iv.lo && open && !iv.loOpen)) {
        iv.lo = v; iv.loOpen = open; iv.loReason = reason;
    }
}

void mergeUpperBound(AccumulatedInterval& iv,
                     const mpq_class& v, bool open, SatLit reason) {
    if (!iv.hasHi) {
        iv.hasHi = true; iv.hi = v; iv.hiOpen = open; iv.hiReason = reason;
        return;
    }
    if (v < iv.hi || (v == iv.hi && open && !iv.hiOpen)) {
        iv.hi = v; iv.hiOpen = open; iv.hiReason = reason;
    }
}

void absorbBound(AccumulatedInterval& iv, const LinearBound& lb) {
    if (iv.emptied) return;
    switch (lb.kind) {
        case LinearBound::Kind::Lower:
            mergeLowerBound(iv, lb.value, lb.open, lb.reason);
            break;
        case LinearBound::Kind::Upper:
            mergeUpperBound(iv, lb.value, lb.open, lb.reason);
            break;
        case LinearBound::Kind::Equal:
            mergeLowerBound(iv, lb.value, false, lb.reason);
            mergeUpperBound(iv, lb.value, false, lb.reason);
            break;
    }
    // Detect emptiness: lo > hi, or lo == hi with at least one open.
    if (iv.hasLo && iv.hasHi) {
        bool empty = false;
        if (iv.lo > iv.hi) empty = true;
        else if (iv.lo == iv.hi && (iv.loOpen || iv.hiOpen)) empty = true;
        if (empty) {
            iv.emptied = true;
            iv.emptyReasons = {iv.loReason, iv.hiReason};
            // Dedupe identical reasons (same atom)
            if (iv.emptyReasons.size() == 2 &&
                iv.emptyReasons[0] == iv.emptyReasons[1]) {
                iv.emptyReasons.pop_back();
            }
        }
    }
}

std::optional<mpq_class> chooseFeasiblePoint(const AccumulatedInterval& iv) {
    if (iv.emptied) return std::nullopt;
    if (iv.hasLo && iv.hasHi) {
        if (iv.lo == iv.hi) return iv.lo;  // equality, one point
        return (iv.lo + iv.hi) / mpq_class(2);
    }
    if (iv.hasLo) {
        return iv.loOpen ? iv.lo + mpq_class(1) : iv.lo;
    }
    if (iv.hasHi) {
        return iv.hiOpen ? iv.hi - mpq_class(1) : iv.hi;
    }
    return mpq_class(0);  // unbounded both ways
}

} // namespace

namespace {

// Limitation-(a) DFS helper. Walk asserted polynomial atoms over a
// hypothetical sample. Returns true iff every fully-evaluable atom
// (one whose vars are all in `sample`) holds under that sample.
//
// Sound by construction: this only checks satisfaction, never claims
// UNSAT. A failing atom rejects the current sample branch in the DFS.
bool fullSampleSatisfiesAtoms(PolynomialKernel& kernel,
                              const std::vector<class AssertedAtom>&,
                              const std::unordered_map<VarId, mpq_class>&);

} // namespace

// Bounded DFS to find a complete feasible assignment over the candidate
// set. Returns true and populates `out` on success; false otherwise.
// Cap node-visits to avoid combinatorial blowup on large problems.
static constexpr int DFS_NODE_BUDGET = 50000;

namespace {

bool dfsAssign(PolynomialKernel& kernel,
               AlgebraBackend* algebra,
               const std::vector<class AssertedAtom>& atoms,
               const std::vector<mpq_class>& baseCands,
               std::unordered_map<VarId, mpq_class>& sample,
               const std::vector<VarId>& remaining,
               size_t idx,
               int& budget);

} // namespace

mcsat::ValueChoice NlsatEngine::pickValue(VarId var,
                                          const mcsat::MCSatTrail& trail) {
    pendingExplainClause_.clear();
    if (!kernel_) {
        return mcsat::ValueChoice::giveUp("NlsatEngine: no kernel");
    }

    // 0. Cache lookup — if a previous pickValue in the same engine state
    //    already discovered a complete feasible assignment via DFS, just
    //    return the cached value for this var.
    if (cachedAssignmentSucceeded_) {
        auto it = cachedAssignment_.find(var);
        if (it != cachedAssignment_.end()) {
            return mcsat::ValueChoice::found(it->second);
        }
        // Cache says feasible but doesn't bind var — bug guard; fall through.
    }

    // 1. Simple-bound analysis: detect "v rel c" atoms, intersect them.
    AccumulatedInterval iv;
    std::vector<AssertedAtom> simpleAtomsContributing;
    for (const auto& a : asserted_) {
        auto lb = detectSimpleBound(*kernel_, a, var);
        if (lb) {
            absorbBound(iv, *lb);
            simpleAtomsContributing.push_back(a);
            if (iv.emptied) break;
        }
    }
    if (iv.emptied) {
        pendingExplainClause_ = iv.emptyReasons;
        std::vector<TheoryAtomRecord> blocking;
        for (const auto& a : simpleAtomsContributing) {
            blocking.push_back(a.atom);
        }
        return mcsat::ValueChoice::conflict(std::move(blocking));
    }

    // 2. DFS for a COMPLETE feasible assignment (Limitation-(a) fix).
    //    Run BEFORE the greedy single-var candidate loop so a smarter
    //    decision wins over "first survivor" — solves the x+y=4 ∧ x-y=2
    //    pattern where x=0 superficially survives but no y works.
    //    Sound: DFS returns true only when every atom is validated under
    //    the full sample; on success the cached assignment drives every
    //    subsequent pickValue call.
    if (!cachedAssignmentTried_) {
        cachedAssignmentTried_ = true;

        // Build the trail's current sample.
        std::unordered_map<VarId, mpq_class> sample;
        bool trailOk = true;
        for (const auto& e : trail.entries()) {
            if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
                e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
            auto q = e.value.tryAsRational();
            if (!q) { trailOk = false; break; }
            sample[e.var] = *q;
        }

        if (trailOk) {
            // Use the same constraint-simplicity ordering as
            // pickNextVar (mgc-A). The cache is rebuilt if invalidated.
            (void)pickNextVar(trail);  // ensure varOrderCache_ populated
            std::vector<VarId> remaining;
            for (VarId v : varOrderCache_) {
                if (!sample.count(v)) remaining.push_back(v);
            }
            // Put `var` first so we return its value if the DFS succeeds.
            auto it = std::find(remaining.begin(), remaining.end(), var);
            if (it != remaining.end()) {
                std::iter_swap(remaining.begin(), it);
            }

            std::vector<mpq_class> baseCands = {
                mpq_class(0),
                mpq_class(1), mpq_class(-1),
                mpq_class(2), mpq_class(-2),
                mpq_class(1, 2), mpq_class(-1, 2),
                mpq_class(3), mpq_class(-3),
                mpq_class(4), mpq_class(-4),
                mpq_class(5), mpq_class(-5),
            };

            int budget = DFS_NODE_BUDGET;
            if (dfsAssign(*kernel_, algebra_, asserted_, baseCands, sample,
                          remaining, 0, budget)) {
                cachedAssignmentSucceeded_ = true;
                for (const auto& [v, q] : sample) {
                    cachedAssignment_[v] = RealValue::fromMpq(q);
                }
                auto cit = cachedAssignment_.find(var);
                if (cit != cachedAssignment_.end()) {
                    return mcsat::ValueChoice::found(cit->second);
                }
            }
        }
    }

    // 4. mgc-H CdcacCore fallback. When DFS exhausts, delegate to the
    //    production-validated CDCAC engine. Build a CdcacInput
    //    normalized to `poly REL 0` per CdcacConstraint, call solve,
    //    and on Sat extract rational coordinates into the cache.
    //    Sound: CdcacCore enforces every §15 invariant itself
    //    (sign-invariance, exact algebra). Algebraic (non-rational)
    //    coordinates are skipped — remaining vars then fall through
    //    to GiveUp → Unknown, never a wrong verdict.
    //
    // XOLVER_NRA_MCSAT_NO_CDCAC=1 disables the fallback for
    // diagnosis of high-degree benchmarks where CdcacCore hangs.
    const char* noFallback = std::getenv("XOLVER_NRA_MCSAT_NO_CDCAC");
    bool fallbackEnabled = !(noFallback && *noFallback && *noFallback != '0');
    if (fallbackEnabled && algebra_ && kernel_ && !cachedAssignmentSucceeded_) {
        if (!cdcacFallback_) {
            cdcacFallback_ = std::make_unique<CdcacCore>(kernel_, algebra_);
        }
        CdcacInput input;
        bool inputOk = true;
        for (const auto& a : asserted_) {
            auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
            if (!pp) continue;
            auto rhsQ = pp->rhs.tryAsRational();
            if (!rhsQ) { inputOk = false; break; }
            CdcacConstraint c;
            c.poly = polyMinusRhs(*kernel_, pp->poly, *rhsQ);
            c.rel = a.value ? pp->rel : negateRelation(pp->rel);
            c.reason = a.assertedLit;
            c.level = a.level;
            input.constraints.push_back(std::move(c));
        }
        if (inputOk && !input.constraints.empty()) {
            (void)pickNextVar(trail);  // populate varOrderCache_
            input.varOrder = varOrderCache_;
            auto cdResult = cdcacFallback_->solve(input);
            if (cdResult.status == CdcacStatus::Sat && cdResult.model) {
                cachedAssignmentSucceeded_ = true;
                const SamplePoint& m = *cdResult.model;
                for (size_t i = 0; i < m.varOrder.size(); ++i) {
                    VarId vid = m.varOrder[i];
                    const RealAlg& ra = m.values[i];
                    if (ra.isRational()) {
                        cachedAssignment_[vid] = RealValue::fromMpq(ra.rational);
                    }
                }
                auto cit = cachedAssignment_.find(var);
                if (cit != cachedAssignment_.end()) {
                    return mcsat::ValueChoice::found(cit->second);
                }
            }
        }
    }

    return mcsat::ValueChoice::giveUp(
        "NlsatEngine: no rational candidate survived the asserted atoms");
}

namespace {

bool fullSampleSatisfiesAtoms(PolynomialKernel& kernel,
                              const std::vector<AssertedAtom>& atoms,
                              const std::unordered_map<VarId, mpq_class>& sample) {
    for (const auto& a : atoms) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) return false;
        auto vars = kernel.variables(pp->poly);
        bool covered = true;
        for (const auto& n : vars) {
            auto vid = kernel.findVar(n);
            if (!vid || !sample.count(*vid)) { covered = false; break; }
        }
        if (!covered) continue;  // not yet evaluable — surviving
        PolyId effective = polyMinusRhs(kernel, pp->poly, *rhsQ);
        int sgnInt = kernel.sgnVarId(effective, sample);
        Sign s = signFromInt(sgnInt);
        if (!atomHoldsForSign(s, pp->rel, a.value)) return false;
    }
    return true;
}

// mgc-B: per-variable sign hint derived from single-variable
// inequality atoms. Positive=+1, Negative=-1, NoneOrZero=0.
int signHintForVar(PolynomialKernel& kernel,
                   const std::vector<AssertedAtom>& atoms,
                   VarId v) {
    std::string name(kernel.varName(v));
    int hint = 0;
    for (const auto& a : atoms) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        auto vars = kernel.variables(pp->poly);
        if (vars.size() != 1 || vars[0] != name) continue;
        // Single-var atom — compute the effective bound direction.
        // Poly is a*v + b, rhs is c. The asserted relation is rel
        // (if a.value true) or its negation. After moving rhs:
        // a*v rel' (c - b). Then v's positivity follows from sign(a)
        // and the effective relation's direction.
        auto coefs = kernel.getIntegerCoefficients(pp->poly, name);
        if (!coefs || coefs->size() != 2) continue;
        mpz_class a_z = (*coefs)[0];
        mpz_class b_z = (*coefs)[1];
        if (a_z == 0) continue;
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) continue;
        mpq_class bound = (*rhsQ - mpq_class(b_z)) / mpq_class(a_z);
        Relation rel = a.value ? pp->rel : negateRelation(pp->rel);
        if (a_z < 0) rel = flipRelation(rel);
        // Now `v rel bound`. If bound >= 0 and rel is > or >=, v > 0.
        // If bound <= 0 and rel is < or <=, v < 0.
        if ((rel == Relation::Gt || rel == Relation::Geq) && bound >= 0) {
            hint = +1;
        } else if ((rel == Relation::Lt || rel == Relation::Leq) && bound <= 0) {
            if (hint == 0) hint = -1;
        }
    }
    return hint;
}

// Build a sign-biased base candidate list. Positive bias: try {1, 2, 3, 5, 10}
// first, then {0, -1, -2, ...}. Negative bias: mirror. No bias: standard order.
std::vector<mpq_class> baseCandidatesForSign(int signHint) {
    // Cap candidate magnitudes at ±5: in high-degree polynomial atoms
    // (e.g. mgc's vv3^9) a candidate of 10 generates 10^9+ intermediate
    // values that exceed GMP working memory under exact-rational
    // arithmetic. Five-bit candidates stay safe up to ~degree 16.
    static const mpq_class POSITIVE_FIRST[] = {
        mpq_class(1), mpq_class(2), mpq_class(3),
        mpq_class(1, 2), mpq_class(5),
        mpq_class(0),
        mpq_class(-1), mpq_class(-2), mpq_class(-3),
    };
    static const mpq_class NEGATIVE_FIRST[] = {
        mpq_class(-1), mpq_class(-2), mpq_class(-3),
        mpq_class(-1, 2), mpq_class(-5),
        mpq_class(0),
        mpq_class(1), mpq_class(2), mpq_class(3),
    };
    static const mpq_class NEUTRAL[] = {
        mpq_class(0),
        mpq_class(1), mpq_class(-1),
        mpq_class(2), mpq_class(-2),
        mpq_class(1, 2), mpq_class(-1, 2),
        mpq_class(3), mpq_class(-3),
        mpq_class(5), mpq_class(-5),
    };
    std::vector<mpq_class> out;
    if (signHint > 0) {
        for (const auto& c : POSITIVE_FIRST) out.push_back(c);
    } else if (signHint < 0) {
        for (const auto& c : NEGATIVE_FIRST) out.push_back(c);
    } else {
        for (const auto& c : NEUTRAL) out.push_back(c);
    }
    return out;
}

// Build the NRA SamplePoint shape (varOrder + RealAlg values) from a
// rational map. Used to seed isolateRealRootsAlgebraic so the algebra
// backend can specialize multivariate constraints to univariate in v.
SamplePoint sampleFromMap(const std::unordered_map<VarId, mpq_class>& m,
                          const std::vector<VarId>& exclude) {
    SamplePoint sp;
    for (const auto& [v, q] : m) {
        if (std::find(exclude.begin(), exclude.end(), v) != exclude.end()) continue;
        sp.push(v, RealAlg::fromRational(q));
    }
    return sp;
}

// Collect rational candidate values for variable v under the current
// partial sample: for each asserted atom whose un-bound variables are
// exactly {v}, specialize its polynomial via the algebra backend and
// isolate real roots. Rational roots become new candidates. Algebraic
// roots are skipped (the current MCSatTrail value channel is
// rational-only).
std::vector<mpq_class> collectRootCandidates(
    PolynomialKernel& kernel, AlgebraBackend* algebra,
    const std::vector<AssertedAtom>& atoms,
    const std::unordered_map<VarId, mpq_class>& sample,
    VarId v) {
    std::vector<mpq_class> out;
    if (!algebra) return out;
    // Sample without v.
    SamplePoint prefix = sampleFromMap(sample, {v});
    for (const auto& a : atoms) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        auto names = kernel.variables(pp->poly);
        // Check: every name except v's name is in sample.
        std::string vName(kernel.varName(v));
        bool onlyV = true;
        bool containsV = false;
        for (const auto& n : names) {
            if (n == vName) { containsV = true; continue; }
            auto vid = kernel.findVar(n);
            if (!vid || !sample.count(*vid)) { onlyV = false; break; }
        }
        if (!onlyV || !containsV) continue;

        // Build (poly - rhs) so isolateRealRoots gives boundary values
        // of the relation directly.
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) continue;
        PolyId effective = polyMinusRhs(kernel, pp->poly, *rhsQ);
        RootSet rs = algebra->isolateRealRootsAlgebraic(effective, prefix, v);
        if (rs.crashOccurred) continue;
        for (const auto& r : rs.roots) {
            if (r.isRational()) out.push_back(r.rational);
        }
    }
    return out;
}

bool dfsAssign(PolynomialKernel& kernel,
               AlgebraBackend* algebra,
               const std::vector<AssertedAtom>& atoms,
               const std::vector<mpq_class>& /*baseCands*/,
               std::unordered_map<VarId, mpq_class>& sample,
               const std::vector<VarId>& remaining,
               size_t idx,
               int& budget) {
    if (budget-- <= 0) return false;
    if (idx >= remaining.size()) {
        return fullSampleSatisfiesAtoms(kernel, atoms, sample);
    }
    VarId v = remaining[idx];

    // mgc-B: build per-var base candidate list with sign-bias from any
    // single-variable inequality on v. Then prepend algebraic-root
    // candidates from atoms that became univariate in v under sample.
    int signHint = signHintForVar(kernel, atoms, v);
    std::vector<mpq_class> sCands = baseCandidatesForSign(signHint);
    std::vector<mpq_class> rootCands =
        collectRootCandidates(kernel, algebra, atoms, sample, v);
    std::vector<mpq_class> candidates;
    candidates.reserve(rootCands.size() + sCands.size());
    for (auto& r : rootCands) candidates.push_back(std::move(r));
    for (const auto& c : sCands) candidates.push_back(c);

    for (const auto& cand : candidates) {
        if (budget <= 0) return false;
        sample[v] = cand;
        if (fullSampleSatisfiesAtoms(kernel, atoms, sample)) {
            if (dfsAssign(kernel, algebra, atoms, sCands, sample,
                          remaining, idx + 1, budget)) {
                return true;
            }
        }
        sample.erase(v);
    }
    return false;
}

} // namespace

std::vector<SatLit> NlsatEngine::explainConflict(
    const mcsat::MCSatTrail& trail,
    const std::vector<TheoryAtomRecord>& blockingAtoms) {
    (void)trail;
    (void)blockingAtoms;
    // Return the clause computed during pickValue. Empty if no
    // theory-valid explanation was constructed; the framework then
    // downgrades to Unknown (sound).
    return pendingExplainClause_;
}

bool NlsatEngine::validateModel(const mcsat::MCSatTrail& trail,
                                TheorySolver::TheoryModel& outModel) {
    if (!kernel_) return false;
    auto sample = buildSample(trail, NullVar, nullptr);
    if (!sample) return false;
    for (const auto& a : asserted_) {
        auto* pp = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!pp) continue;
        auto rhsQ = pp->rhs.tryAsRational();
        if (!rhsQ) return false;
        auto polyVars = kernel_->variables(pp->poly);
        if (!sampleCoversAll(polyVars, *sample, *kernel_)) {
            return false;
        }
        PolyId effective = polyMinusRhs(*kernel_, pp->poly, *rhsQ);
        int sgnInt = kernel_->sgnVarId(effective, *sample);
        Sign s = signFromInt(sgnInt);
        if (!atomHoldsForSign(s, pp->rel, a.value)) return false;
    }
    for (const auto& e : trail.entries()) {
        if (e.kind != mcsat::TrailEntryKind::TheoryDecision &&
            e.kind != mcsat::TrailEntryKind::TheoryPropagation) continue;
        std::string name(kernel_->varName(e.var));
        outModel.numericAssignments[name] = e.value;
    }
    return true;
}

} // namespace nlsat
} // namespace xolver
