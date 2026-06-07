#pragma once

// NraLocalSearch — Layer A rational-only local repair for NRA.
//
// Heuristic SAT-finder for nonlinear real arithmetic. Maintains a rational
// assignment (mpq_class per VarId, NEVER algebraic), evaluates each active
// constraint via RationalPolynomial::substituteRational, and walks one variable
// at a time toward a sign-satisfying value.
//
// The search is SAT-direction only — it returns either a candidate rational
// model that the caller must EXACT-VALIDATE (invariant 1) or std::nullopt. It
// NEVER emits UNSAT (invariant 2) and NEVER ascends an internal sample into a
// final verdict (invariant 6).
//
// Layer B (XOLVER_NRA_LS_EQ_RELAX, default-OFF) and Layer C (cell-jump) are
// deferred to Phase NRA-LS-B / Phase NRA-LS-D respectively; this header carries
// the Phase A surface only.
//
// Master gates: XOLVER_NRA_LOCALSEARCH default-OFF; caller stashes the returned
// rational model into satFastModel_ and lets the Solver-level realDivPurifySatFloor
// re-validate against original assertions before SAT is reported.

#include "expr/types.h"
#include "theory/arith/poly/PolynomialKernel.h"   // LS-C: MonomialTerm in termsCache_
#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/core/TheoryAtomTypes.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <vector>

namespace xolver {

class PolynomialKernel;

class NraLocalSearch {
public:
    struct Constraint {
        PolyId poly;          // (poly REL 0) form, rhs already subtracted
        Relation rel;
        SatLit reason;
    };

    NraLocalSearch(PolynomialKernel& kernel) : kernel_(kernel) {}
    ~NraLocalSearch();   // LS-C: env-gated cache-stats dump (XOLVER_NRA_LS_STATS)

    // Wall-clock budget in ms (XOLVER_NRA_LS_BUDGET_MS). 0 or negative = unlimited.
    void setBudgetMs(long ms) { budgetMs_ = ms; }
    // Max search rounds — a coarse iteration cap; the real budget is wall-clock.
    void setMaxRounds(int n)  { maxRounds_ = n; }
    // Equality relaxation (Phase NRA-LS-B). Default false (strict equality).
    void setEqRelax(bool b)   { eqRelax_ = b; }
    // ε for equality relaxation (Phase NRA-LS-B). Default 1/1024.
    void setEpsilon(mpq_class q) { epsilon_ = std::move(q); }

    // Try to find a rational assignment satisfying every active constraint.
    // Returns std::nullopt on failure — the caller falls through to CAC.
    // A non-empty return is a CANDIDATE: the caller MUST exact-validate it
    // (invariant 1). The kernel must outlive every call.
    std::optional<std::unordered_map<VarId, mpq_class>>
    tryFindModel(const std::vector<Constraint>& constraints,
                 const std::vector<VarId>& vars);

private:
    PolynomialKernel& kernel_;
    long budgetMs_ = 50;      // Task D-derisked default (raised from 10 → 50ms after the
                              // local 14-case sweep showed 0 regression and the broad atan-problem-1
                              // cluster showed identical pass + bounded overhead). Env var
                              // XOLVER_NRA_LS_BUDGET_MS still overrides at solver setup.
    int  maxRounds_ = 10;     // coarse iteration cap (was 50; convergent rationals slowed evaluator).
    bool eqRelax_ = false;
    mpq_class epsilon_{1, 1024};
    const mpq_class kZero_{0};   // sentinel for missing var lookups

    // Deterministic PRNG for WalkSAT noise moves (escape local minima). Seeded to a
    // fixed constant so runs are reproducible (no Math.random nondeterminism).
    mutable uint64_t lsRng_ = 0x9E3779B97F4A7C15ULL;
    uint64_t nextRand() const {   // xorshift64*
        uint64_t x = lsRng_; x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
        lsRng_ = x; return x * 0x2545F4914F6CDD1DULL;
    }

    // Phase NRA-LS-C — incremental boundary score cache. evalAt and scaleAt
    // are called per (constraint × candidate × round); without caching, each
    // call rebuilds the same RP from PolyId or re-extracts the kernel terms
    // for an immutable poly. The two caches live on the LS instance (kernel
    // outlives them; entries are valid for the kernel's lifetime). Mutable
    // because evalAt/scaleAt/totalScore are const methods.
    mutable std::unordered_map<PolyId, RationalPolynomial> rpCache_;
    mutable std::unordered_map<PolyId, std::vector<PolynomialKernel::MonomialTerm>> termsCache_;
    mutable uint64_t evalCacheHits_ = 0;
    mutable uint64_t evalCacheMisses_ = 0;
    mutable uint64_t scaleCacheHits_ = 0;
    mutable uint64_t scaleCacheMisses_ = 0;

    // Phase NRA-LS-D (Task F) — atom-violation incremental cache. atomViolation
    // is called per (atom × candidate × round); when LS proposes a move
    // var=q, atoms NOT containing var keep their cached violation (sub-asg
    // unchanged), atoms containing var miss and recompute. Cache key is
    // (PolyId, Relation, sub-asg restricted to atom's vars); equality is
    // exact (sub-asg compared element-by-element) so collisions never return
    // a wrong violation. Per-poly var-set cached separately for cheap reuse.
    mutable std::unordered_map<PolyId, std::vector<VarId>> atomVarsCache_;
    struct ViolationKey {
        PolyId poly;
        Relation rel;
        std::vector<std::pair<VarId, mpq_class>> subAsg;   // canonical sorted by VarId
        bool operator==(const ViolationKey& o) const {
            return poly == o.poly && rel == o.rel && subAsg == o.subAsg;
        }
    };
    struct ViolationKeyHash {
        size_t operator()(const ViolationKey& k) const noexcept;
    };
    mutable std::unordered_map<ViolationKey, mpq_class, ViolationKeyHash> violationCache_;
    mutable uint64_t violationCacheHits_ = 0;
    mutable uint64_t violationCacheMisses_ = 0;

    // Build the sub-asg vector restricted to `vars` from the full `asg`.
    std::vector<std::pair<VarId, mpq_class>> buildSubAsg(
        const std::vector<VarId>& vars,
        const std::unordered_map<VarId, mpq_class>& asg) const;
    // Compute (and cache) the var-set of a constraint's polynomial.
    const std::vector<VarId>& atomVars(PolyId p) const;

    // Evaluate poly at a rational assignment → exact mpq value (NaN-safe: if a
    // variable is missing from `asg`, defaults to 0; if the result isn't a
    // constant, returns nullopt — should never happen with a complete asg).
    std::optional<mpq_class> evalAt(PolyId p,
                                    const std::unordered_map<VarId, mpq_class>& asg) const;

    // Per-atom violation: 0 if the constraint is satisfied at `asg`, else a
    // positive measure of how badly it is violated (signed distance, or the
    // absolute value for equality / disequality). Equality relaxation slips an
    // ε-band around zero when eqRelax_ is on. Used by candidate moves to pick
    // a strictly-better assignment.
    mpq_class atomViolation(const Constraint& c,
                            const std::unordered_map<VarId, mpq_class>& asg) const;

    // Lexicographic score (master-spec):
    //   primary   = weighted count of false atoms (clause = atom in this stage)
    //   secondary = sum of normalized atom violations (magnitude/scale, capped)
    // The compare order means LS prefers SAT-by-count first, residual second —
    // a single huge polynomial cannot dominate the search at the cost of
    // already-satisfied atoms. (Raw-magnitude total was the pre-review bug.)
    struct Score {
        int falseWeightedCount = 0;
        mpq_class normalizedMag{0};
        bool operator<(const Score& o) const {
            if (falseWeightedCount != o.falseWeightedCount)
                return falseWeightedCount < o.falseWeightedCount;
            return normalizedMag < o.normalizedMag;
        }
        bool isSat() const { return falseWeightedCount == 0; }
    };
    Score totalScore(const std::vector<Constraint>& cs,
                     const std::vector<int>& weights,
                     const std::unordered_map<VarId, mpq_class>& asg) const;

    // Normalization scale for a polynomial at a rational point:
    //   scale(p, α) = 1 + Σ |c_m| · |m(α)|
    // Always ≥ 1 (no division by zero) and grows with the worst-case term
    // magnitude, so the normalized residual sits in [0, 1] for the common case
    // and cannot drown out other atoms' contributions.
    mpq_class scaleAt(PolyId p,
                      const std::unordered_map<VarId, mpq_class>& asg) const;

    // Candidate value pool for `var` given the current assignment. Phase A
    // seed: small integers near 0 + perturbations of the current value (×2,
    // ÷2, +1, -1, +ε, -ε). Augmented by `univariateBoundaryCandidates` per
    // master-spec for the recovery lever.
    std::vector<mpq_class> candidateValues(VarId var,
                                           const std::unordered_map<VarId, mpq_class>& asg) const;

    // Master-spec univariate sign-boundary candidate generation. Substitute
    // every OTHER variable in `c.poly` from `asg`, get the univariate q(t)
    // in `var`, find the feasible-side rational samples for `c.rel`. Degree
    // ≤ 2 are exact via discriminant; degree 3-4 are deferred. Bounded by
    // a per-call budget so a single false atom can't dominate one round.
    std::vector<mpq_class>
    univariateBoundaryCandidates(const Constraint& c, VarId var,
                                  const std::unordered_map<VarId, mpq_class>& asg) const;

    // Sprint 5: detect pairs of linear bound atoms (var ≷ K1, var ≷ K2) on
    // the SAME variable and produce the midpoint as a special candidate.
    // For tight-bound clusters (meti-tarski's pi in (3.1415926, 3.1415927)
    // — interval width 10⁻⁷, midpoint denom 2·10⁷ — the regular
    // pushNear offsets are too coarse and the regular MAX_DEN cap rejects
    // the midpoint). This bypass is targeted at exactly that pattern.
    // boundDir (optional out): per single-sided-bounded var, +1 if it can be
    // increased while staying feasible (lower bound only) or -1 if it can be
    // decreased (upper bound only). Lets the caller diversify restart magnitudes
    // feasibly. Vars absent from the map are two-sided or unbounded.
    std::vector<std::pair<VarId, mpq_class>>
    bracketMidpointCandidates(const std::vector<Constraint>& cs,
                              const std::vector<VarId>& vars,
                              std::unordered_map<VarId, int>* boundDir = nullptr) const;

    // Phase NRA-LS-B (XOLVER_NRA_LS_EQ_RELAX, default OFF): after a relaxed
    // satisfier (|p| ≤ ε for every equality atom), exact-restore by finding
    // a variable that p is linear in and solving p = 0 analytically. Mirrors
    // master-spec step (b). Step (a) — zero-substitution — happens implicitly
    // because asg starts at zero. Step (c) — micro-tune — defers to the
    // walking loop after step (b). Step (d) — CDCAC exact validation —
    // happens at the caller (NraSolver::check `validateCandidate`).
    bool exactRestoreEqualities(const std::vector<Constraint>& cs,
                                std::unordered_map<VarId, mpq_class>& asg) const;

    // Walk one round: pick a violated constraint, try every var × every
    // candidate value, accept the strictly-best move (lowest total violation).
    // Returns true if any move improved the total; false if local minimum.
    bool walkOneRound(const std::vector<Constraint>& cs,
                      const std::vector<int>& weights,
                      const std::vector<VarId>& vars,
                      std::unordered_map<VarId, mpq_class>& asg,
                      Score& currentScore);
};

} // namespace xolver
