#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/projection/LocalProjection.h"
#include "theory/arith/nra/preprocess/NullificationAnalyzer.h"
#include "theory/arith/nra/proof/CellCertificateValidator.h"
#include "theory/arith/nra/projection/ProjectionPolicy.h"
#include "theory/arith/nra/valuation/RationalRootIsolation.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "util/EnvParam.h"   // XOLVER_NRA_LAZARD_MAX_COEFF_BITS cap for the SAT-first libpoly guard
#include <chrono>
#include <algorithm>
#include <cmath>
#include <unordered_set>
#include <iostream>
#include <cstdlib>
#include <string>

namespace xolver {

// TEMP diag: which projection-incompleteness site drops unsatTrustworthy_ (file-based;
// worker-thread stderr is suppressed). XOLVER_NRA_TOWER_DIAG = output path.
static inline void logIncSite(int n) {
    if (const char* df = std::getenv("XOLVER_NRA_TOWER_DIAG")) if (*df)
        if (std::FILE* fp = std::fopen(df, "a")) { std::fprintf(fp, "[INCSITE] %d\n", n); std::fclose(fp); }
}

// M2 diagnostics (XOLVER_NRA_ICP_DIAG=1): count box-ICP calls vs prunes to tell
// "firing but insufficient" (→ needs M3 learning) from "never bites" (→ structure).
static thread_local long g_icpCalls = 0;
static thread_local long g_icpPrunes = 0;

// ------------------------------------------------------------------
// Helpers (free functions in xolver namespace)
// ------------------------------------------------------------------

// Helper: collect all distinct polynomials from constraints
static std::vector<PolyId> collectPolys(const std::vector<CdcacConstraint>& constraints) {
    std::vector<PolyId> polys;
    std::unordered_set<PolyId> seen;
    for (const auto& c : constraints) {
        if (!seen.insert(c.poly).second) continue;
        polys.push_back(c.poly);
    }
    return polys;
}

// Helper: pick a rational sample from a sector (lo, hi)
static mpq_class simplestRationalIn(const mpq_class& lo, const mpq_class& hi);  // fwd

// Covering sector representative. Any value in the OPEN interval (lo,hi) is a sound
// representative (the sector is sign-invariant), so pick the SIMPLEST rational rather
// than the midpoint — z3/NLSAT's pick_in_complement heuristic: 0 if it lies inside,
// else the integer closest to 0, else the smallest-denominator dyadic 1/2^k. Real
// models cluster at such simple values, so a SAT case is more likely to land its
// witness coordinate directly; and the simpler sample keeps the deeper specialized
// polynomials simpler ("to simplify the polynomials"), unlike a midpoint that can be a
// high-denominator rational between two algebraic-derived bounds.
static mpq_class pickRationalSample(const mpq_class& lo, const mpq_class& hi) {
    return simplestRationalIn(lo, hi);
}

// z3 pick_in_complement for a sector unbounded BELOW, (−∞, hi): the simplest value
// strictly below hi — 0 if it lies inside (hi>0), else the integer closest to 0 that
// is still < hi. Real models cluster at 0 / small integers, so the first sector should
// try 0 (the common witness) before marching away from the root.
static mpq_class simplestBelow(const mpq_class& hi) {
    if (sgn(hi) > 0) return mpq_class(0);                       // 0 ∈ (−∞,hi), simplest of all
    mpz_class chi; mpz_cdiv_q(chi.get_mpz_t(), hi.get_num().get_mpz_t(), hi.get_den().get_mpz_t());
    return mpq_class(chi - 1);                                  // largest integer strictly < hi
}
// z3 pick_in_complement for a sector unbounded ABOVE, (lo, +∞).
static mpq_class simplestAbove(const mpq_class& lo) {
    if (sgn(lo) < 0) return mpq_class(0);                       // 0 ∈ (lo,+∞)
    mpz_class flo; mpz_fdiv_q(flo.get_mpz_t(), lo.get_num().get_mpz_t(), lo.get_den().get_mpz_t());
    return mpq_class(flo + 1);                                  // smallest integer strictly > lo
}

// V3: Helper: convert Bound to AlgebraicEndpoint
static AlgebraicEndpoint boundToEndpoint(const Bound& bound) {
    AlgebraicEndpoint ep;
    if (bound.isNegInf()) {
        ep.kind = EndpointKind::MinusInfinity;
    } else if (bound.isPosInf()) {
        ep.kind = EndpointKind::PlusInfinity;
    } else {
        ep.kind = EndpointKind::Algebraic;
        ep.value = bound.value;
    }
    return ep;
}

// V3: Helper: convert Cell to FiberCellCoverage
static FiberCellCoverage cellToFiberCoverage(const Cell& cell, size_t index) {
    FiberCellCoverage fc;
    switch (cell.kind) {
        case CellKind::FullLine:
            fc.kind = FiberCellKind::FullLine;
            break;
        case CellKind::Sector:
            if (cell.lower.isNegInf()) {
                fc.kind = FiberCellKind::MinusInfinitySector;
            } else if (cell.upper.isPosInf()) {
                fc.kind = FiberCellKind::PlusInfinitySector;
            } else {
                fc.kind = FiberCellKind::Sector;
            }
            break;
        case CellKind::Section:
            fc.kind = FiberCellKind::Section;
            break;
    }
    fc.cell = cell;
    fc.lower = boundToEndpoint(cell.lower);
    fc.upper = boundToEndpoint(cell.upper);
    fc.lowerOpen = cell.lower.open;
    fc.upperOpen = cell.upper.open;
    if (cell.isSection() && cell.section) {
        fc.sectionDefiningPoly = cell.section->liftedDefiningPoly;
    }
    fc.certifiedCellIndex = index;
    return fc;
}

// Helper: try local projection to get univariate polynomials for current level
// V4: uses ProjectionPolicy instead of raw LocalProjectionEngine.
struct TryLocalProjectionResult {
    std::vector<RootSet> rootSets;
    bool generatedProjectionPolys = false;
};

[[maybe_unused]] static TryLocalProjectionResult tryLocalProjection(
    const std::vector<CdcacConstraint>& constraints,
    const SamplePoint& prefix,
    VarId var,
    int level,
    PolynomialKernel* kernel,
    AlgebraBackend* algebra,
    ProjectionPolicy* policy) {

    TryLocalProjectionResult result;

    // Convert constraints to RationalPolynomial
    std::vector<ReasonedPolynomial> rpConstraints;
    for (const auto& c : constraints) {
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel);
        if (!rpOpt) continue;
        rpConstraints.push_back({*rpOpt, PolyRole::ConstraintPolynomial, {c.reason}});
    }

    if (rpConstraints.empty()) return result;

    // Find the highest variable present in any constraint (above current level)
    std::set<VarId> allVars;
    for (const auto& rp : rpConstraints) {
        auto vars = rp.poly.variables();
        allVars.insert(vars.begin(), vars.end());
    }

    // Build projection context
    ProjectionContext ctx;
    ctx.level = level;
    ctx.currentVar = var;
    ctx.prefix = prefix;
    ctx.kernel = kernel;
    ctx.algebra = algebra;

    for (VarId eliminateVar : allVars) {
        if (eliminateVar == var) continue;

        ProjectionInput input;
        input.polys = rpConstraints;
        input.eliminateVar = eliminateVar;
        input.baseCell = Cell();  // V4: baseCell for obligation scope
        input.baseCell.var = var;

        auto projResult = policy->project(input, ctx);
        if (projResult.hasDegeneracy) {
            // V4: if policy reports fallback, still try to use any polys produced
            if (!projResult.fallbackCondition.has_value()) {
                continue;
            }
        }

        // Try to convert projected polynomials to univariate in current var
        for (const auto& rp : projResult.projectionPolys) {
            if (!rp.poly.contains(var)) continue;
            result.generatedProjectionPolys = true;

            // Convert to PolyId
            PolyId polyId = rp.poly.toPolyId(*kernel);
            if (polyId == NullPoly) continue;

            // Specialize to univariate (substituting prefix values for lower vars)
            UniPolyId up = algebra->specializeToUnivariate(polyId, prefix, var);
            if (up == NullUniPolyId) continue;

            RootSet roots = algebra->isolateRealRoots(up);
            if (roots.numRoots() > 0) {
                result.rootSets.push_back(std::move(roots));
            }
        }
    }

    return result;
}

// ------------------------------------------------------------------
// CdcacCore implementation
// ------------------------------------------------------------------

CdcacCore::CdcacCore(PolynomialKernel* kernel, AlgebraBackend* algebra)
    : kernel_(kernel), algebra_(algebra) {
    // Lazard tower lifting is OFF by default (the projection stage stays Collins).
    // Opt in with XOLVER_NRA_LAZARD_LIFT=1; it only ADDS certified root
    // isolations for genuine towers (>=2 algebraic prefix coords) that ViaNorm
    // punts on — flag-off behaviour is byte-identical to the Collins baseline.
    if (const char* e = std::getenv("XOLVER_NRA_LAZARD_LIFT"))
        lazardLiftEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
    // Projection mode selection + HYBRID gate (DEFAULT). The default path is the
    // fail-safe hybrid: Collins first, Lazard fallback ONLY on Collins-Unknown
    // (see solve() / hybridEnabled_). The env hatches force a single fixed mode:
    //   XOLVER_NRA_PROJECTION=lazard  => pure Lazard  (projectionKind_=LazardStyle,
    //                                    lift+per-cell-cert on, no Collins pass).
    //   XOLVER_NRA_PROJECTION=collins => pure Collins (the old default).
    //   XOLVER_NRA_HYBRID=0           => pure Collins (A/B baseline).
    // Any other value / unset => hybrid. An explicit setProjectionPolicy() call
    // still overrides the lazily-created policy regardless of mode. The projection
    // SET affects completeness only — the UNSAT certification gate
    // (unsatTrustworthy_ + per-cell cert) is unchanged.
    if (const char* e = std::getenv("XOLVER_NRA_PROJECTION")) {
        std::string mode(e);
        if (mode == "lazard" || mode == "Lazard" || mode == "LAZARD") {
            // Pure Lazard: configure the full Lazard path and disable the hybrid
            // Collins-first pass (the user explicitly asked for Lazard-only).
            projectionKind_ = ProjectionPolicyKind::LazardStyle;
            lazardLiftEnabled_ = true;
            hybridEnabled_ = false;
        } else if (mode == "collins" || mode == "Collins" || mode == "COLLINS") {
            // Pure Collins (the old default): no Lazard fallback.
            projectionKind_ = ProjectionPolicyKind::CollinsConservative;
            hybridEnabled_ = false;
        }
    }
    // Hybrid projection (Collins-first, Lazard fallback on Collins-Unknown) is
    // promoted default-ON; an explicit XOLVER_NRA_PROJECTION=collins above still
    // forces pure Collins.
    // FAIL-SAFE per-cell UNSAT gate (Lazard mode). Default ON; only relevant in
    // Lazard mode (the Collins gate is untouched). Force off for A/B with
    // XOLVER_NRA_LAZARD_CELL_CERT=0.
    if (const char* e = std::getenv("XOLVER_NRA_LAZARD_CELL_CERT"))
        lazardCellCertEnabled_ = !(e[0] == '0' || e[0] == 'f' || e[0] == 'F' || e[0] == 'n' || e[0] == 'N');
    // nlsat-engine STEP A: SAT-only sample-first model search (default-OFF, gated).
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST"))
        satFirstEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_BUDGET")) {
        long b = std::atol(e);
        if (b > 0) satFirstBudget_ = b;
    }
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_MAX_BITS")) {
        long b = std::atol(e);
        if (b > 0) satSampleMaxBits_ = b;
    }
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_MS")) {
        long b = std::atol(e);
        if (b >= 0) satFirstMs_ = b;   // 0 ⇒ no wall cap (node budget only)
    }
    // nlsat-engine INCREMENT 3: lazy conflict-driven projection learning on top
    // of SAT-first (default-OFF). Implies sat-first.
    if (const char* e = std::getenv("XOLVER_NRA_CAC_NLSAT")) {
        satNlsatEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
        if (satNlsatEnabled_) satFirstEnabled_ = true;
    }
    // nlsat-engine INCREMENT 4: algebraic-model SAT-first (default-OFF). Implies
    // sat-first. Lets the model search reach algebraic-coordinate models (Geogebra).
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_ALG"))
        satFirstAlgEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_ALG_DEG")) {
        long b = std::atol(e);
        if (b > 0) satFirstAlgDegCap_ = b;
    }
    // M1+M2: forward infeasibility lookahead for the rational SAT-first (default-OFF).
    if (const char* e = std::getenv("XOLVER_NRA_CAC_SAT_FIRST_LOOKAHEAD")) {
        satFirstLookaheadEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
        if (satFirstLookaheadEnabled_) satFirstEnabled_ = true;
    }
}

void CdcacCore::setProjectionPolicy(std::unique_ptr<ProjectionPolicy> policy) {
    policy_ = std::move(policy);
}

std::optional<RootSet> CdcacCore::mergeRoots(const std::vector<RootSet>& rootSets) {
    // Collect all roots
    std::vector<RealAlg> all;
    for (const auto& rs : rootSets) {
        for (const auto& r : rs.roots) {
            all.push_back(r);
        }
    }

    // Insertion-style sort+dedup: comparator may return Unknown, so std::sort
    // (strict weak ordering) is not safe.
    // If any comparison returns Unknown, the whole merge fails.
    std::vector<RealAlg> merged;
    for (auto& candidate : all) {
        bool inserted = false;
        for (auto it = merged.begin(); it != merged.end(); ++it) {
            CompareResult c = algebra_->compareRealAlg(candidate, *it);
            if (c == CompareResult::Equal) {
                // Duplicate: merge origins into the surviving root
                if (candidate.isAlgebraic() && it->isAlgebraic()) {
                    auto& surv = it->root.origins;
                    const auto& cand = candidate.root.origins;
                    for (const auto& o : cand) {
                        // avoid duplicates
                        bool exists = false;
                        for (const auto& s : surv) {
                            if (s.liftedDefiningPoly == o.liftedDefiningPoly &&
                                s.mainVar == o.mainVar &&
                                s.level == o.level) {
                                exists = true;
                                break;
                            }
                        }
                        if (!exists) surv.push_back(o);
                    }
                }
                inserted = true;
                break;
            }
            if (c == CompareResult::Less) {
                merged.insert(it, std::move(candidate));
                inserted = true;
                break;
            }
            if (c == CompareResult::Unknown) {
                // Cannot determine order: fail the merge
                return std::nullopt;
            }
            // Greater: continue to next position
        }
        if (!inserted) {
            merged.push_back(std::move(candidate));
        }
    }

    // Refine algebraic intervals so adjacent roots have disjoint isolating intervals.
    // This ensures sector loops can always construct non-empty rational sectors.
    for (size_t i = 1; i < merged.size(); ++i) {
        bool prevAlg = merged[i - 1].isAlgebraic();
        bool currAlg = merged[i].isAlgebraic();
        if (!prevAlg && !currAlg) continue; // both rational, already sorted

        if (prevAlg && currAlg) {
            auto& prev = merged[i - 1].root;
            auto& curr = merged[i].root;
            for (int iter = 0; iter < 40; ++iter) {
                if (prev.upper < curr.lower) break;
                bool okPrev = algebra_->refineRootInterval(prev);
                bool okCurr = algebra_->refineRootInterval(curr);
                if (!okPrev && !okCurr) {
                    return std::nullopt;
                }
            }
            if (prev.upper >= curr.lower) {
                return std::nullopt;
            }
        } else if (!prevAlg && currAlg) {
            // prev is rational, curr is algebraic
            mpq_class q = merged[i - 1].rational;
            auto& curr = merged[i].root;
            for (int iter = 0; iter < 40; ++iter) {
                if (q < curr.lower) break;
                bool okCurr = algebra_->refineRootInterval(curr);
                if (!okCurr) break;
            }
            if (q >= curr.lower) {
                // Cannot separate by refinement alone.  Use compareRealAlg
                // sign-fallback to determine order.
                RealAlg qAlg = RealAlg::fromRational(q);
                RealAlg rootAlg = RealAlg::fromAlgebraic(curr);
                CompareResult c = algebra_->compareRealAlg(qAlg, rootAlg);
                if (c == CompareResult::Less) {
                    // q < root, but curr.lower may still equal q.
                    // Bisect to push curr.lower strictly above q so the sector
                    // loop can construct a non-empty rational sector.
                    mpq_class lo = q;
                    mpq_class hi = curr.upper;
                    for (int bisect = 0; bisect < 40; ++bisect) {
                        if (lo >= hi) break;
                        mpq_class mid = (lo + hi) / 2;
                        RealAlg midAlg = RealAlg::fromRational(mid);
                        CompareResult mc = algebra_->compareRealAlg(midAlg, rootAlg);
                        if (mc == CompareResult::Equal) {
                            lo = mid;
                            break;
                        }
                        if (mc == CompareResult::Less) {
                            lo = mid;
                        } else if (mc == CompareResult::Greater) {
                            hi = mid;
                        } else {
                            break;
                        }
                    }
                    curr.lower = lo;
                    continue;
                }
                if (c == CompareResult::Greater) {
                    // q > root: inconsistent with insertion sort ordering
                    return std::nullopt;
                }
                // Still Unknown: fail conservatively
                return std::nullopt;
            }
        } else {
            // prev is algebraic, curr is rational
            auto& prev = merged[i - 1].root;
            mpq_class q = merged[i].rational;
            for (int iter = 0; iter < 40; ++iter) {
                if (prev.upper < q) break;
                bool okPrev = algebra_->refineRootInterval(prev);
                if (!okPrev) break;
            }
            if (prev.upper >= q) {
                // Same fallback as above
                RealAlg rootAlg = RealAlg::fromAlgebraic(prev);
                RealAlg qAlg = RealAlg::fromRational(q);
                CompareResult c = algebra_->compareRealAlg(rootAlg, qAlg);
                if (c == CompareResult::Less) {
                    // root < q, but prev.upper may still equal q.
                    // Bisect to push prev.upper strictly below q.
                    mpq_class lo = prev.lower;
                    mpq_class hi = q;
                    for (int bisect = 0; bisect < 40; ++bisect) {
                        if (lo >= hi) break;
                        mpq_class mid = (lo + hi) / 2;
                        RealAlg midAlg = RealAlg::fromRational(mid);
                        CompareResult mc = algebra_->compareRealAlg(rootAlg, midAlg);
                        if (mc == CompareResult::Equal) {
                            hi = mid;
                            break;
                        }
                        if (mc == CompareResult::Less) {
                            lo = mid;
                        } else if (mc == CompareResult::Greater) {
                            hi = mid;
                        } else {
                            break;
                        }
                    }
                    prev.upper = hi;
                    continue;
                }
                if (c == CompareResult::Greater) {
                    return std::nullopt;
                }
                return std::nullopt;
            }
        }
    }

    return RootSet{std::move(merged)};
}

// EXTREME OOM-survival backstop for the eager projection closure. The matrix
// closure's toPolyId OOM was ROOT-CAUSE-FIXED algorithmically (the kernel pool
// leak in toPrimitiveInteger — see RationalPolynomial::toPrimitiveInteger /
// PolynomialKernel::mkFromMonomials): matrix-1/2/3 now convert in tens of MB and
// run to a normal timeout instead of SIGSEGV. So this is NOT a solvability cap
// and is NOT meant to floor anything that the (now memory-safe) engine can do —
// the thresholds are set FAR above every real case (matrix's biggest poly is
// ~45k terms; this fires only past 2 MILLION terms / 50 Mbit coefficients, i.e.
// a poly that cannot be materialized in any reasonable RAM even with the O(n)
// build). It exists purely so a genuinely pathological projection kills the SOLVE
// gracefully (Unknown) instead of the PROCESS (a SIGSEGV would lose a whole
// competition batch). Env-tunable for experiments.
static bool projectedPolyIntractable(const RationalPolynomial& rp) {
    static const long kMaxTerms =
        env::paramInt("XOLVER_NRA_PROJ_MAX_TERMS", 2000000) > 0
            ? (long)env::paramInt("XOLVER_NRA_PROJ_MAX_TERMS", 2000000) : 2000000L;
    static const long kMaxDeg =
        env::paramInt("XOLVER_NRA_PROJ_MAX_DEG", 100000) > 0
            ? (long)env::paramInt("XOLVER_NRA_PROJ_MAX_DEG", 100000) : 100000L;
    // Summed coefficient bit-length (numerator AND denominator) — the matrix
    // resultants have huge INTEGER coefficients (den==1 ⇒ a denominator-only guard
    // misses them), so we bound num+den. 50 Mbit (~6 MB raw) is an extreme ceiling.
    static const long kMaxCoeffBits =
        env::paramInt("XOLVER_NRA_PROJ_MAX_COEFF_BITS", 50000000) > 0
            ? (long)env::paramInt("XOLVER_NRA_PROJ_MAX_COEFF_BITS", 50000000) : 50000000L;
    if ((long)rp.terms().size() > kMaxTerms) return true;
    long coeffBits = 0, totalDeg = 0;
    for (const auto& [key, coeff] : rp.terms()) {
        long md = 0;
        for (const auto& [v, e] : key) { (void)v; md += (long)e; }
        if (md > totalDeg) totalDeg = md;
        if (totalDeg > kMaxDeg) return true;
        const mpz_class& num = coeff.get_num();
        const mpz_class& den = coeff.get_den();
        if (num != 0) coeffBits += (long)mpz_sizeinbase(num.get_mpz_t(), 2);
        if (den > 1)  coeffBits += (long)mpz_sizeinbase(den.get_mpz_t(), 2);
        if (coeffBits > kMaxCoeffBits) return true;   // unrepresentable after denom-clear
    }
    return false;
}

void CdcacCore::buildClosure(const CdcacInput& input) {
    if (std::getenv("XOLVER_NRA_LAZARD_DIAG"))
        std::cerr << "[LAZARD-CLOSURE-ENTRY] vars=" << input.varOrder.size()
                  << " constraints=" << input.constraints.size() << std::endl;
    unsatTrustworthy_ = true;
    // Per-cell gate (Lazard): track whether the Lazard closure underpinning ALL
    // levels' boundaries built to completion. Starts true, dropped to false at
    // the SAME points that drop unsatTrustworthy_ during closure construction.
    // (Independent of unsatTrustworthy_ so a later lift-only incompleteness in
    // an exploratory branch does not retroactively poison the closure flag.)
    closureComplete_ = true;
    int n = static_cast<int>(input.varOrder.size());
    levelPolyIds_.assign(static_cast<size_t>(std::max(0, n)), {});
    polyOrigins_.clear();   // Feature A: rebuilt below (Collins path)

    std::vector<RationalPolynomial> rps;
    std::vector<size_t> rpsToConstraint;   // Feature A: rps index → input constraint index
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        const auto& c = input.constraints[ci];
        if (kernel_->isConstant(c.poly)) continue;   // constants pre-handled by caller
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { unsatTrustworthy_ = false; logIncSite(1); closureComplete_ = false; continue; }
        rps.push_back(std::move(*rp));
        rpsToConstraint.push_back(ci);
    }

    // Projection-set selection. Default: the Collins closure (unconditionally
    // sound, byte-identical to today). XOLVER_NRA_PROJECTION=lazard builds the
    // Lazard projection closure instead, driving the SAME root-isolation/covering
    // path so SAT (full-model-validated) is unaffected.
    //
    // SOUNDNESS (T3): the Lazard projection set is smaller than McCallum/Collins
    // and is sound+complete for UNSAT only with (a) a COMPLETE Lazard closure AND
    // (b) Lazard-consistent lifting at every level. Closure completeness is folded
    // in here (incomplete ⇒ unsatTrustworthy_ = false, mirroring the Collins
    // branch below); lift completeness is folded in per-level in solveLevel
    // (ordinary specialize == the [H3] multiplicity-0 case; a vanished poly's
    // boundary must be recovered by the valuation, else unsatTrustworthy_=false).
    // The non-Lazard parts of the lift (vanish==Unknown, uncertified specialize,
    // unsupported tower isolation) already drop the flag. So a complete Lazard
    // closure + a fully-complete lift ⇒ a sound Lazard UNSAT; ANY incompleteness
    // ⇒ Unknown at the line-892 gate. CDCAC's Collins path stays the backstop.
    if (projectionKind_ == ProjectionPolicyKind::LazardStyle) {
        LazardProjectionClosure::Config lcfg;
        // [H4]: pass the libpoly kernel so the Lazard projection's
        // GCD/content/squarefree/resultant go through libpoly's EXACT ops
        // (high-degree multivariate inputs blow up the hand-rolled PRS).
        auto lreason = lazardClosure_.build(rps, input.varOrder, lcfg, kernel_);
        if (std::getenv("XOLVER_NRA_LAZARD_DIAG")) {
            std::cerr << "[LAZARD-CLOSURE] "
                      << (lreason == LazardIncompleteReason::None ? "COMPLETE"
                          : lreason == LazardIncompleteReason::ProjectionKernelFailure ? "KERNEL_FAILURE"
                          : lreason == LazardIncompleteReason::ProjectionBudgetExceeded ? "BUDGET_EXCEEDED"
                          : "OTHER")
                      << " entries=" << lazardClosure_.entries().size() << std::endl;
        }
        if (lreason != LazardIncompleteReason::None) {
            unsatTrustworthy_ = false; logIncSite(2);   // incomplete Lazard projection ⇒ no UNSAT
            closureComplete_ = false;    // per-cell gate: closure not complete
        }
        for (int k = 0; k < n; ++k) {
            for (int id : lazardClosure_.levelPolys(k)) {
                // Crash firewall: refuse to materialize an intractable projected
                // poly (toPolyId would OOM/SIGSEGV). Incomplete ⇒ no UNSAT rests
                // on it; SAT comes from the model search, not this closure.
                if (projectedPolyIntractable(lazardClosure_.entries()[id].poly)) {
                    unsatTrustworthy_ = false; logIncSite(3); closureComplete_ = false; continue;
                }
                PolyId pid = lazardClosure_.entries()[id].poly.toPolyId(*kernel_);
                if (pid == NullPoly) { unsatTrustworthy_ = false; logIncSite(4); closureComplete_ = false; continue; }
                levelPolyIds_[k].push_back(pid);
            }
        }
        return;
    }

    auto reason = closure_.build(rps, input.varOrder, ProjectionClosure::Config(), kernel_);
    if (reason != ProjectionIncompleteReason::None) {
        unsatTrustworthy_ = false; logIncSite(5);   // incomplete projection ⇒ no UNSAT may rest on it
    }

    for (int k = 0; k < n; ++k) {
        for (int id : closure_.levelPolys(k)) {
            // Crash firewall: an intractable projected poly (matrix closure) would
            // OOM/SIGSEGV inside toPolyId. Skip it ⇒ closure incomplete ⇒ Unknown,
            // never an unsound UNSAT. The real model comes from SAT-first.
            if (projectedPolyIntractable(closure_.entries()[id].poly)) {
                unsatTrustworthy_ = false; logIncSite(6); continue;
            }
            PolyId pid = closure_.entries()[id].poly.toPolyId(*kernel_);
            if (pid == NullPoly) { unsatTrustworthy_ = false; logIncSite(7); continue; }
            levelPolyIds_[k].push_back(pid);
            // Feature A (A1): translate this entry's rps-indexed input origins to input
            // constraint indices and union into the level poly's provenance.
            std::vector<int>& dst = polyOrigins_[pid];
            for (int r : closure_.inputOrigins(id)) {
                if (r >= 0 && r < static_cast<int>(rpsToConstraint.size())) {
                    const int cidx = static_cast<int>(rpsToConstraint[r]);
                    if (std::find(dst.begin(), dst.end(), cidx) == dst.end()) dst.push_back(cidx);
                }
            }
        }
    }
}

void CdcacCore::resetPerSolveState() {
    // Drop the lazily-created policy so the next pass re-creates it for the
    // (possibly changed) projectionKind_. The closures / levelPolyIds_ /
    // completeness flags are all rebuilt by buildClosure(), but the policy is
    // created in solveLevel() and would otherwise survive a mode flip.
    policy_.reset();
    // buildClosure() resets unsatTrustworthy_/closureComplete_ and re-.assign()s
    // levelPolyIds_; closure_/lazardClosure_ are rebuilt in place by their build().
    // Nothing else carries cross-pass search state. (Reset the trust flags here too
    // so they are clean even if a future buildClosure early-out skips them.)
    unsatTrustworthy_ = true;
    closureComplete_ = false;
    constraintVarsCache_.clear();   // forward-prune per-constraint var sets
    constraintsByLevel_.clear();    // forward-prune per-level constraint index
    polyOrigins_.clear();           // Feature A: level-poly → constraint provenance
}

// Lazily build + return the VarId set of constraint `ci` (cached per input).
// Used by solveLevel's forward-prune to test "is this constraint fully
// determined by the prefix?". A constraint whose RationalPolynomial cannot be
// formed is tagged {NullVar} so the all-assigned test never passes (conservative
// — it is then never forward-pruned, only caught at the leaf).
const std::vector<VarId>& CdcacCore::constraintVars(size_t ci, const CdcacInput& input) {
    if (constraintVarsCache_.size() != input.constraints.size()) {
        constraintVarsCache_.assign(input.constraints.size(), {});
        for (size_t i = 0; i < input.constraints.size(); ++i) {
            auto rp = RationalPolynomial::fromPolyId(input.constraints[i].poly, *kernel_);
            if (rp) {
                const auto vs = rp->variables();   // std::set<VarId>
                constraintVarsCache_[i].assign(vs.begin(), vs.end());
            } else {
                constraintVarsCache_[i] = {NullVar};
            }
        }
    }
    return constraintVarsCache_[ci];
}

// Lazily build + return the constraints whose DEEPEST var (by input.varOrder
// position) is at level `k` — exactly the set that becomes fully determined when
// level k's variable is assigned. Lets the forward-prune iterate O(determined-at-k)
// constraints per cell instead of re-scanning all of them. A constraint with a var
// outside varOrder (incl. the {NullVar} "poly-unformable" tag) is excluded → never
// forward-pruned, identical to the old hasVar/allAssigned test failing for it.
const std::vector<size_t>& CdcacCore::constraintsAtLevel(size_t k, const CdcacInput& input) {
    if (constraintsByLevel_.empty()) {
        const size_t n = input.varOrder.size();
        constraintsByLevel_.assign(n, {});
        std::unordered_map<VarId, int> pos;
        pos.reserve(n * 2);
        for (size_t i = 0; i < n; ++i) pos[input.varOrder[i]] = static_cast<int>(i);
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            const auto& cv = constraintVars(ci, input);
            int deepest = -1;
            bool ok = !cv.empty();
            for (VarId v : cv) {
                auto it = pos.find(v);
                if (it == pos.end()) { ok = false; break; }   // var not in order (or NullVar) → never prune
                if (it->second > deepest) deepest = it->second;
            }
            if (ok && deepest >= 0 && deepest < static_cast<int>(n))
                constraintsByLevel_[static_cast<size_t>(deepest)].push_back(ci);
        }
    }
    static const std::vector<size_t> kEmpty;
    return (k < constraintsByLevel_.size()) ? constraintsByLevel_[k] : kEmpty;
}

// Feature A (A2): the level-poly subset whose provenance ⊆ the reason constraints.
std::vector<PolyId> CdcacCore::reasonProjectionSubset(
    const std::unordered_map<PolyId, std::vector<int>>& origins,
    const std::vector<PolyId>& levelPolys,
    const std::vector<int>& reasonConstraints) {
    std::vector<PolyId> out;
    std::unordered_set<int> reasonSet(reasonConstraints.begin(), reasonConstraints.end());
    for (PolyId pid : levelPolys) {
        auto it = origins.find(pid);
        if (it == origins.end() || it->second.empty()) continue;   // unknown provenance ⇒ exclude (keep its roots)
        bool subset = true;
        for (int ci : it->second) {
            if (!reasonSet.count(ci)) { subset = false; break; }
        }
        if (subset) out.push_back(pid);
    }
    return out;
}

// Feature A (A2): map a conflict's reason literals to input constraint indices.
std::vector<int> CdcacCore::reasonConstraintIndices(const std::vector<SatLit>& reasons,
                                                    const CdcacInput& input) const {
    std::vector<int> out;
    out.reserve(reasons.size());
    for (SatLit lit : reasons) {
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            if (input.constraints[ci].reason == lit) { out.push_back(static_cast<int>(ci)); break; }
        }
    }
    return out;
}

CdcacResult CdcacCore::solvePass(const CdcacInput& input) {
    // Build the exact-RationalPolynomial cache used by the interval forward-prune
    // (intervalFpViolation). Once per solve (reused across hybrid Collins/Lazard
    // passes); the overlay's precompute, if it ran, is harmlessly overwritten.
    if (!satRpBuilt_) {
        satRp_.assign(input.constraints.size(), std::nullopt);
        satSafe_.assign(input.constraints.size(), false);
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            auto rp = RationalPolynomial::fromPolyId(input.constraints[ci].poly, *kernel_);
            if (!rp) continue;
            long td = 0;
            for (const auto& [key, coeff] : rp->terms()) {
                (void)coeff; long md = 0;
                for (const auto& [v, e] : key) { (void)v; md += e; }
                if (md > td) td = md;
            }
            satSafe_[ci] = (td <= 20);   // skip very-high-degree (wide intervals, slow ivEval)
            satRp_[ci] = std::move(rp);
        }
        satRpBuilt_ = true;
    }
    double tBC0 = std::chrono::duration<double, std::milli>(
                      std::chrono::steady_clock::now().time_since_epoch()).count();
    buildClosure(input);
    double dBC = std::chrono::duration<double, std::milli>(
                     std::chrono::steady_clock::now().time_since_epoch()).count() - tBC0;
    if (dBC > 500.0) {
        const char* f = std::getenv("XOLVER_NRA_TOWER_DIAG");
        if (f && *f) if (std::FILE* fp = std::fopen(f, "a")) {
            std::fprintf(fp, "[SLOW-BUILDCLOSURE] vars=%zu cons=%zu lazard=%d ms=%.0f\n",
                         input.varOrder.size(), input.constraints.size(),
                         (projectionKind_ == ProjectionPolicyKind::LazardStyle || lazardLiftEnabled_) ? 1 : 0, dBC);
            std::fclose(fp);
        }
    }
    SamplePoint prefix;
    CdcacResult result = solveLevel(0, prefix, input);

    // CDCAC covering-UNSAT soundness rests on the per-level/per-cell completeness
    // tracking inside solveLevel (unsatTrustworthy_ + the Lazard per-cell
    // certificate gate), which downgrades any covering whose delineation was
    // incomplete to Unknown. (presolve/linear UNSAT never reaches CDCAC.)
    if (const char* df = std::getenv("XOLVER_NRA_TOWER_DIAG")) if (*df)
        if (std::FILE* f = std::fopen(df, "a")) {
            std::fprintf(f, "[SOLVEPASS] status=%d reason=%d vars=%zu cons=%zu\n",
                         (int)result.status, (int)result.unknownReason,
                         input.varOrder.size(), input.constraints.size());
            std::fclose(f);
        }
    return result;
}

// Covering profiler (XOLVER_NRA_TOWER_DIAG-gated, per-thread): counts the covering
// tree size so the deep-tower TO can be attributed to tree explosion vs per-op cost.
// "measure don't guess" — the ViaTower timer showed the tower itself is cheap.
namespace {
thread_local long gSolveLevelCalls = 0;   // recursion nodes (internal)
thread_local long gCellsTested     = 0;   // testAndRecurse invocations (cells lifted)
thread_local long gFullSamples     = 0;   // leaf full-sample checks
thread_local double gBoundaryMs    = 0;   // time in per-level boundary collection (specialize+isolate)
inline double covNowMs() {
    return std::chrono::duration<double, std::milli>(
               std::chrono::steady_clock::now().time_since_epoch()).count();
}
}

CdcacResult CdcacCore::solve(const CdcacInput& input) {
    satRpBuilt_ = false;   // rebuild the interval-FP cache for this solve's constraints
    gSolveLevelCalls = gCellsTested = gFullSamples = 0; gBoundaryMs = 0;   // reset per solve
    struct CovDump {
        const CdcacInput& in;
        ~CovDump() {
            const char* f = std::getenv("XOLVER_NRA_TOWER_DIAG");
            if (!f || !*f) return;
            if (std::FILE* fp = std::fopen(f, "a")) {
                std::fprintf(fp, "[COVERING] vars=%zu cons=%zu solveLevel=%ld cells=%ld fullSamples=%ld boundaryMs=%.0f\n",
                             in.varOrder.size(), in.constraints.size(),
                             gSolveLevelCalls, gCellsTested, gFullSamples, gBoundaryMs);
                std::fclose(fp);
            }
        }
    } covDump{input};
    if (std::getenv("XOLVER_NRA_TOWER_DIAG"))
        std::cerr << "[CDCAC-SOLVE] entry vars=" << input.varOrder.size()
                  << " cons=" << input.constraints.size() << std::endl;
#ifndef NDEBUG
    std::cerr << "[CDCAC] solve: varOrder.size=" << input.varOrder.size() << std::endl;
#endif
    // STEP 2 — box-consistency GLOBAL refutation (conflict generalization at the root):
    // before any covering, run the HC4 box fixpoint (now incl. degree-2 square
    // contraction) over the empty assignment. An infeasible over-approximation box ⇒
    // the whole problem is UNSAT — a SHORT refutation that short-circuits the covering-
    // tree blowup (the hong family: Σx²<1 ⇒ |x_i|<1 ⇒ |Πx|<1, contra Πx>1). Sound: box
    // ⊇ feasible set, so an empty box proves no real solution exists. The conflict
    // clause is the negation of the jointly-infeasible constraints (loose but valid).
    // ≥2 vars only: a univariate problem is solved trivially (and with a V3 covering
    // certificate) by the covering itself, so the box short-circuit would only strip
    // that certificate; the box's value is the MULTI-variable bound contradiction (the
    // covering tree explodes there, e.g. hong) where it short-circuits the blowup.
    if (input.varOrder.size() >= 2 && topLevelBoxInfeasible(input)) {
        std::vector<SatLit> reasons;
        reasons.reserve(input.constraints.size());
        for (const auto& c : input.constraints) reasons.push_back(c.reason);
        // Carry the conflict literals in a one-cell covering too: consumers re-derive
        // the conflict clause via ReasonManager::minimize(covering), which reads
        // cells[].reasons — an EMPTY covering there would yield an empty (false) clause
        // and the UNSAT gets downgraded to Unknown. So put the reasons in BOTH places.
        Covering cover;
        Cell cell;                       // full-line cell carrying the global conflict
        cell.reasons = reasons;
        cover.cells.push_back(std::move(cell));
        return CdcacResult::mkUnsat(std::move(cover), std::move(reasons));
    }
    // nlsat-engine STEP A: SAT-only sample-first model search, ONE-SHOT per
    // CdcacCore lifetime, BEFORE the eager buildClosure projection. Sound: Sat is
    // returned only on a checkFullSample-validated full point; otherwise falls
    // through to the projection engine, byte-identical to before. Default-OFF.
    if ((satFirstEnabled_ || satFirstAlgEnabled_) && !satFirstTried_ && !input.varOrder.empty()) {
        satFirstTried_ = true;
        satDerivedCells_.clear();   // increment 3: fresh learned dead-cell set per solve
        // Precompute per-constraint safety once: a poly whose denominator-cleared
        // integer coefficients would exceed the cap is skipped for delineation (the
        // libpoly heap-corruption class — same cap as the projection firewall). The
        // leaf checkFullSample still signAt-validates ALL constraints (signAt is
        // internally crash-firewalled → Unknown), so skipping only affects which
        // polys delineate cells, never soundness.
        static const long capBits = [] {
            int v = env::paramInt("XOLVER_NRA_LAZARD_MAX_COEFF_BITS", 65536);
            return v > 0 ? static_cast<long>(v) : 65536L;
        }();
        satSafe_.assign(input.constraints.size(), false);
        satRp_.assign(input.constraints.size(), std::nullopt);
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            const auto& c = input.constraints[ci];
            auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
            if (!rp) continue;   // no exact form (satSafe_[ci] stays false ⇒ skip search)
            // Degree cap: libpoly root isolation / specialization on a high-degree
            // multivariate (matrix-product polys) crashes regardless of coefficient
            // size. Total degree = max over monomials of the sum of exponents.
            static const long degCap =
                env::paramInt("XOLVER_NRA_CAC_SAT_FIRST_MAX_DEG", 12) > 0
                    ? env::paramInt("XOLVER_NRA_CAC_SAT_FIRST_MAX_DEG", 12) : 12;
            long totalDeg = 0;
            mpz_class D = 1;
            for (const auto& [key, coeff] : rp->terms()) {
                long md = 0; for (const auto& [v, e] : key) { (void)v; md += e; }
                if (md > totalDeg) totalDeg = md;
                const mpz_class den = coeff.get_den();
                if (den > 1) { mpz_class t; mpz_lcm(t.get_mpz_t(), D.get_mpz_t(), den.get_mpz_t()); D = t; }
            }
            bool safe = totalDeg <= degCap;
            if (safe) {
                for (const auto& [key, coeff] : rp->terms()) {
                    (void)key;
                    const mpz_class cleared = coeff.get_num() * (D / coeff.get_den());
                    if (cleared != 0 &&
                        static_cast<long>(mpz_sizeinbase(cleared.get_mpz_t(), 2)) > capBits) { safe = false; break; }
                }
            }
            satRp_[ci] = std::move(rp);   // cache exact poly for crash-free Horner sign eval
            satSafe_[ci] = safe;
        }
        // SAT-first runs ONLY when EVERY constraint is safe to evaluate. The leaf
        // must exact-check ALL constraints for soundness, but sign evaluation of a
        // high-degree poly (kernel_->sgn / libpoly coefficient_sgn → rational_interval_pow)
        // OOM-crashes — so a problem with ANY unsafe constraint cannot be soundly
        // model-searched here; bail to the projection engine (matrix-1-all etc.).
        bool allSafe = true;
        for (size_t ci = 0; ci < satSafe_.size(); ++ci)
            if (!satSafe_[ci]) { allSafe = false; break; }
        // Increment 4: the algebraic path additionally requires EVERY constraint's
        // total degree ≤ satFirstAlgDegCap_ — algebra_->signAt (libpoly algebraic
        // sign) OOM-crashes on high degree, so the algebraic regime is restricted
        // to low-degree systems (Geogebra-class). High-degree ⇒ fall back to the
        // crash-free rational path.
        bool algOk = satFirstAlgEnabled_;
        if (algOk) {
            for (size_t ci = 0; ci < satRp_.size() && algOk; ++ci) {
                if (!satRp_[ci]) continue;
                long md = 0;
                for (const auto& [key, coeff] : satRp_[ci]->terms()) {
                    (void)coeff; long d = 0;
                    for (const auto& [v, e] : key) { (void)v; d += (long)e; }
                    if (d > md) md = d;
                }
                if (md > satFirstAlgDegCap_) algOk = false;
            }
        }
        // Run the algebraic triangular path when degrees allow it (default-on); the
        // rational wandering path runs ONLY when explicitly opted in. When neither
        // applies, skip SAT-first entirely (no overhead — straight to projection).
        if (allSafe && (algOk || satFirstEnabled_)) {
            SamplePoint prefix;
            long budget = satFirstBudget_;
            satFirstT0_ = std::chrono::steady_clock::now();   // wall-clock cap reference
            CdcacResult sat = algOk ? trySatSampleFirstAlg(0, prefix, input, budget)
                                    : trySatSampleFirst(0, prefix, input, budget);
            if (const char* d = std::getenv("XOLVER_NRA_ICP_DIAG"); d && d[0] == '1')
                std::fprintf(stderr, "[ICP-DIAG] nvars=%zu calls=%ld prunes=%ld status=%d\n",
                             input.varOrder.size(), g_icpCalls, g_icpPrunes,
                             static_cast<int>(sat.status));
            if (sat.status == CdcacStatus::Sat)
                return sat;
        }
    }

    // --- Pure single-mode (A/B hatches): one pass with the configured mode. ---
    if (!hybridEnabled_) {
        return solvePass(input);
    }

    // --- FAIL-SAFE HYBRID (DEFAULT): Collins primary, Lazard fallback. --------
    // Pass 1 — Collins. Force the Collins configuration for this pass regardless
    // of any XOLVER_NRA_LAZARD_LIFT the user set, so the primary pass is exactly
    // the old pure-Collins behaviour. Collins's Sat/Unsat are AUTHORITATIVE.
    const bool savedLazardLift = lazardLiftEnabled_;
    projectionKind_ = ProjectionPolicyKind::CollinsConservative;
    lazardLiftEnabled_ = false;
    resetPerSolveState();
    CdcacResult collinsResult = solvePass(input);

    if (collinsResult.status != CdcacStatus::Unknown) {
        // A definite Collins verdict is returned as-is — Lazard never overrides
        // a Collins decision. This is what makes the hybrid strictly >= Collins.
        lazardLiftEnabled_ = savedLazardLift;  // restore configured value
        return collinsResult;
    }

    // Pass 2 — Lazard, ONLY because Collins was Unknown (no double-work on the
    // easy path). Stand up the full Lazard configuration on the SAME input:
    // the Lazard projection set + [H3] valuation lift + the per-cell UNSAT cert
    // gate (lazardCellCertEnabled_ already defaults ON). Reset all per-solve
    // scratch first so the closures / policy / trust flags start clean.
    if (std::getenv("XOLVER_NRA_LAZARD_DIAG"))
        std::cerr << "[CDCAC-HYBRID] Collins Unknown (reason="
                  << static_cast<int>(collinsResult.unknownReason)
                  << ") -> Lazard fallback" << std::endl;
    projectionKind_ = ProjectionPolicyKind::LazardStyle;
    lazardLiftEnabled_ = true;
    resetPerSolveState();
    CdcacResult lazardResult = solvePass(input);

    // Restore the configured mode for the next solve() (this core can be reused
    // across theory-checks; leave it in the default Collins-first state).
    projectionKind_ = ProjectionPolicyKind::CollinsConservative;
    lazardLiftEnabled_ = savedLazardLift;

    // Lazard recovers a Collins-Unknown only to a DEFINITE verdict; otherwise the
    // original Collins Unknown stands. (Lazard Sat is full-model-validated
    // upstream; Lazard Unsat is cert-gated, incomplete => Unknown.)
    if (lazardResult.status != CdcacStatus::Unknown) {
        if (std::getenv("XOLVER_NRA_LAZARD_DIAG"))
            std::cerr << "[CDCAC-HYBRID] Lazard RECOVERED status="
                      << static_cast<int>(lazardResult.status) << std::endl;
        return lazardResult;
    }
    return collinsResult;
}

CdcacResult CdcacCore::solveLevel(int k, SamplePoint& prefix, const CdcacInput& input) {
    ++gSolveLevelCalls;
    {   // time-based tick (every ~2s) survives a TO-kill regardless of tree size
        static thread_local double gLastTickMs = 0;
        double nowt = covNowMs();
        if (nowt - gLastTickMs > 2000.0) {
            gLastTickMs = nowt;
            const char* f = std::getenv("XOLVER_NRA_TOWER_DIAG");
            if (f && *f) if (std::FILE* fp = std::fopen(f, "a")) {
                std::fprintf(fp, "[COVERING-tick] solveLevel=%ld cells=%ld fullSamples=%ld boundaryMs=%.0f\n",
                             gSolveLevelCalls, gCellsTested, gFullSamples, gBoundaryMs);
                std::fclose(fp);
            }
        }
    }
    int n = static_cast<int>(input.varOrder.size());
    if (k == n) {
        ++gFullSamples;
        double tF0 = covNowMs();
        CdcacResult fr = checkFullSample(prefix, input);
        double dF = covNowMs() - tF0;
        if (dF > 500.0) {
            const char* f = std::getenv("XOLVER_NRA_TOWER_DIAG");
            if (f && *f) if (std::FILE* fp = std::fopen(f, "a")) {
                std::fprintf(fp, "[SLOW-FULLSAMPLE] cons=%zu ms=%.0f totalLeaves=%ld\n",
                             input.constraints.size(), dF, gFullSamples);
                std::fclose(fp);
            }
        }
        return fr;
    }

    // V4: ensure a projection policy is available. Default is CollinsConservative;
    // XOLVER_NRA_PROJECTION=lazard selects the Lazard operator (projectionKind_).
    if (!policy_) {
        if (projectionKind_ == ProjectionPolicyKind::LazardStyle) {
            policy_ = std::make_unique<LazardStylePolicy>();
        } else {
            policy_ = std::make_unique<CollinsConservativePolicy>();
        }
    }

    VarId var = input.varOrder[k];
#ifndef NDEBUG
    std::cerr << "[CDCAC] solveLevel k=" << k << " var=" << kernel_->varName(var)
              << " n=" << n << " constraints=" << input.constraints.size() << std::endl;
    std::cerr << "[CDCAC] solveLevel k=" << k << " var=" << kernel_->varName(var) << std::endl;
#endif

    // V2-7: nullification check before specialization
    {
        NullificationAnalyzer na(algebra_);
        for (const auto& c : input.constraints) {
            auto analysis = na.analyzeConstraint(c, prefix, var);
            switch (analysis.action) {
                case NullificationAnalyzer::Action::SkipConstraintAsTrue:
                    continue;
                case NullificationAnalyzer::Action::ReturnFullLineConflict:
                    if (analysis.conflictCell) {
                        // A nullification full-line conflict is a generalization;
                        // it may only conclude UNSAT under a complete closure.
                        if (!unsatTrustworthy_) {
                            return CdcacResult::mkUnknown(
                                CdcacUnknownReason::ProjectionClosureIncomplete);
                        }
                        Cell cell = *analysis.conflictCell;
                        Cell cellCopy = cell;  // copy for certificate
                        Covering cover;
                        cover.var = var;
                        cover.cells.push_back(std::move(cell));
                        CdcacResult result = CdcacResult::mkUnsat(std::move(cover), {c.reason});

                        // V3: Build minimal CoveringCertificate for nullification conflict
                        CellCertificate cert;
                        cert.kind = CellCertificateKind::NullificationConflict;
                        cert.level = k;
                        cert.var = var;
                        cert.cell = cellCopy;
                        AtomCondition ac;
                        ac.atom = NullAtom;
                        ac.poly = c.poly;
                        ac.rel = c.rel;
                        ac.allowedSigns = signSetFromRelation(c.rel);
                        ac.invariantSigns = signToAtomSignSet(Sign::Zero);
                        ac.isConstant = kernel_->isConstant(c.poly);
                        cert.atomConditions.push_back(std::move(ac));
                        CertificateReasonLit crl;
                        crl.lit = c.reason;
                        crl.atom = NullAtom;
                        crl.polarity = true;
                        crl.normalized = {c.poly, c.rel};
                        cert.reasons.push_back(std::move(crl));

                        CoveringCertificate coverCert;
                        coverCert.level = k;
                        coverCert.var = var;
                        // Nullification-conflict cell carries no per-cell Lazard
                        // cert (nullopt) ⇒ not trusted by the per-cell gate; this
                        // path stays gated by unsatTrustworthy_ (conservative).
                        coverCert.cells.push_back(
                            CertifiedCell{std::move(cellCopy), std::move(cert), std::nullopt});

                        // V3: Build CoverageCertificate
                        CoverageCertificate coverage;
                        coverage.level = k;
                        coverage.var = var;
                        coverage.coversWholeFiber = true;
                        coverage.orderedCells.push_back(cellToFiberCoverage(coverCert.cells[0].cell, 0));
                        coverCert.coverage = std::move(coverage);

                        result.coveringCert = std::move(coverCert);
                        return result;
                    }
                    return CdcacResult::mkUnknown(CdcacUnknownReason::NullificationInGeneralization);
                case NullificationAnalyzer::Action::NeedsRepair:
                    // V4: nullification repair is not yet fully wired.
                    // Treat as ContinueNormally for now; obligations are recorded
                    // in analysis.repair for future certificate use.
                    break;
                case NullificationAnalyzer::Action::Unknown:
                    // V2-7: nullification check is best-effort.
                    // If we can't determine nullification (e.g. algebraic prefix),
                    // continue with normal specialization rather than aborting.
                    break;
                case NullificationAnalyzer::Action::ContinueNormally:
                    break;
            }
        }
    }

    // 1. Collect delineating roots for `var` from the COMPLETE projection
    // closure (built once in solve()). closure_.levelPolys(k) holds every
    // coefficient/PSC polynomial whose real roots partition var's axis so that
    // every original constraint is sign-invariant within each resulting cell.
    // Using the closure (not the old single-step tryLocalProjection) is what
    // lets a deep conflict generalize to a SOUND cell instead of the whole
    // axis. When the closure is incomplete OR a specialization is uncertified,
    // unsatTrustworthy_ becomes false and any UNSAT here is downgraded to
    // Unknown at the covering exit.
    // FAIL-SAFE per-cell gate: is THIS level's boundary construction complete?
    // Starts from the closure-completeness flag and is dropped to false at the
    // SAME level-local points that drop unsatTrustworthy_ during boundary
    // collection (spec-failed-and-not-norm-recovered, vanish-not-recovered,
    // vanish-Unknown). The root-isolation/merge failures below already return
    // Unknown directly (so they never reach the per-cell gate). The cell certs
    // built for this level's covering inherit this flag; when in doubt → false.
    const bool lazardModeLevel = (projectionKind_ == ProjectionPolicyKind::LazardStyle)
                                 || lazardLiftEnabled_;
    // When `levelBoundaryComplete` is true at the gate, every boundary poly was
    // either (a) a rational univariate whose roots passed validateRootIsolation
    // (else we returned Unknown directly), or (b) a norm/tower isolation that
    // reported `supported` (the [H2] exact decision). Any unsupported/undecided
    // boundary already drops this flag. So root isolation + merge completeness
    // for this level are implied by levelBoundaryComplete.
    bool levelBoundaryComplete = closureComplete_;

    std::vector<UniPolyId> uniPolys;
    std::vector<RootSet> rootSets;
    std::vector<PolyId> rootSetPolyIds;   // Feature A (A3): the level poly each rootSet came from
    bool hasAlgebraicPrefix = false;
    int algPrefixCount = 0;
    for (const auto& v : prefix.values) {
        if (v.isAlgebraic()) { hasAlgebraicPrefix = true; ++algPrefixCount; }
    }
    static const bool kLazDiag = std::getenv("XOLVER_NRA_LAZARD_DIAG") != nullptr;
    if (kLazDiag && hasAlgebraicPrefix)
        std::cerr << "[LAZVAL] solveLevel k=" << k << " algPrefixCoords=" << algPrefixCount
                  << " levelPolys=" << levelPolyIds_[k].size() << std::endl;

    double tB0 = covNowMs();
    for (PolyId p : levelPolyIds_[k]) {
        if (kernel_->isConstant(p)) continue;
        UniPolyId up = algebra_->specializeToUnivariate(p, prefix, var);
        if (up == NullUniPolyId) {
            // Specialization to a univariate failed (algebraic prefix). Use the
            // SAFE Norm/resultant isolation (single algebraic coordinate),
            // which eliminates the algebraic variable via a rational resultant
            // and isolates over Q — never touching libpoly's crash-prone
            // algebraic root isolation. Unsupported (tower / residual var /
            // degenerate Norm) ⇒ cannot certify ⇒ not trustworthy for UNSAT
            // (SAT still samples + validates). Anti-corruption rule: an
            // unreliable/unsupported backend op yields Unknown, never a crash
            // or a false UNSAT.
            if (hasAlgebraicPrefix) {
                bool supported = false;
                RootSet roots = algebra_->isolateRealRootsViaNorm(p, prefix, var, supported);
                if (kLazDiag)
                    std::cerr << "[LAZVAL] nullSpec k=" << k << " viaNorm supported="
                              << supported << " roots=" << roots.numRoots() << std::endl;
                if (!supported && lazardLiftEnabled_) {
                    // ViaNorm only certifies a single algebraic coordinate; for a
                    // genuine tower (>=2 algebraic coords) try the Lazard tower
                    // isolation. Still sound: unsupported/Unknown => fall through.
                    roots = algebra_->isolateRealRootsViaTower(p, prefix, var, supported);
                }
                if (supported) {
                    if (roots.numRoots() > 0) { rootSets.push_back(std::move(roots)); rootSetPolyIds.push_back(p); }
                    continue;
                }
            }
            unsatTrustworthy_ = false; logIncSite(8);
            // Per-cell gate: a boundary poly whose specialization could not be
            // recovered ⇒ this level's delineation is incomplete ⇒ no per-cell
            // UNSAT trust for ANY cell of this level.
            levelBoundaryComplete = false;
            continue;
        }
        // A poly that vanishes (≡0 in var) at this prefix contributes no
        // boundary here. Under a COMPLETE Collins closure this is sound to
        // skip — the poly's coefficients (all in the closure) already delineate
        // the lower levels. An UNDECIDED vanish ⇒ cannot certify ⇒ Unknown.
        auto vanish = algebra_->vanishesAtPrefix(p, prefix, var);
        if (vanish == VanishResult::Vanishes) {
            // Collins default: under a COMPLETE Collins closure, ALL of p's
            // coefficients are in the closure and already delineate the lower
            // levels, so skipping a vanished p is sound (continue).
            //
            // LAZARD mode: the smaller Lazard projection does NOT contain all
            // coefficients, so that skip-soundness argument fails. A vanished
            // poly's boundary must be POSITIVELY recovered via the [H3] valuation
            // (its Lazard residual = the lowest nonvanishing derivative), only
            // available over an ALGEBRAIC prefix. If we recover it -> push the
            // residual roots. If we do NOT (rational prefix, or tower recovery
            // unsupported / all-derivatives-zero) -> the delineation is incomplete
            // -> unsatTrustworthy_ = false (the line-892 gate downgrades any UNSAT
            // to Unknown). SAT is unaffected (full-model validated).
            bool lazardMode = (projectionKind_ == ProjectionPolicyKind::LazardStyle)
                              || lazardLiftEnabled_;
            if (lazardMode) {
                bool recovered = false;
                if (hasAlgebraicPrefix) {
                    bool supported = false;
                    RootSet roots = algebra_->isolateRealRootsViaTower(p, prefix, var, supported);
                    if (std::getenv("XOLVER_NRA_LAZARD_DIAG"))
                        std::cerr << "[LAZVAL] vanish-route k=" << k << " supported="
                                  << supported << " roots=" << roots.numRoots() << std::endl;
                    if (supported) {
                        recovered = true;
                        if (roots.numRoots() > 0) { rootSets.push_back(std::move(roots)); rootSetPolyIds.push_back(p); }
                    }
                }
                if (!recovered) {
                    unsatTrustworthy_ = false; logIncSite(9);  // boundary not recovered ⇒ no UNSAT
                    // Per-cell gate: a vanished poly's boundary that the [H3]
                    // valuation could not positively recover ⇒ delineation
                    // incomplete ⇒ no per-cell UNSAT trust for this level.
                    levelBoundaryComplete = false;
                }
            }
            continue;
        }
        if (vanish == VanishResult::Unknown) {
            unsatTrustworthy_ = false; logIncSite(10);
            levelBoundaryComplete = false;  // undecided vanish ⇒ incomplete
            continue;
        }

        RootSet roots = algebra_->isolateRealRoots(up);
        // Firewall bail (oversize coeffs ⇒ heap-corruption guard): inconclusive,
        // never "0 roots" (which would shrink the UNSAT cover unsoundly).
        if (roots.crashOccurred) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::RootIsolationInvalid);
        }
        if (!algebra_->validateRootIsolation(up, roots)) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::RootIsolationInvalid);
        }
        for (auto& r : roots.roots) {
            if (r.isAlgebraic()) r.root.origins.push_back({p, var, static_cast<VarId>(k)});
        }
        uniPolys.push_back(up);
        rootSets.push_back(std::move(roots));
        rootSetPolyIds.push_back(p);
    }
    double dB = covNowMs() - tB0;
    gBoundaryMs += dB;
    if (dB > 1000.0) {   // a single level's boundary collection took > 1s — the real hotspot
        const char* f = std::getenv("XOLVER_NRA_TOWER_DIAG");
        if (f && *f) if (std::FILE* fp = std::fopen(f, "a")) {
            std::fprintf(fp, "[SLOW-BOUNDARY] k=%d levelPolys=%zu alg=%d ms=%.0f\n",
                         k, levelPolyIds_[k].size(), algPrefixCount, dB);
            std::fclose(fp);
        }
    }

    // Always route through the covering (incl. the empty-roots full-line cell);
    // its UNSAT conclusion is gated by unsatTrustworthy_. (Replaces the old
    // "no local polys ⇒ CoveringDidNotGrow" early-out and tryLocalProjection.)
    bool projectionSucceeded = true;
    (void)projectionSucceeded;

    // 2. Merge all roots
    auto mergedOpt = mergeRoots(rootSets);
    if (!mergedOpt) {
#ifndef NDEBUG
        std::cerr << "[CDCAC] mergeRoots failed (Unknown comparison)" << std::endl;
#endif
        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
    }
    RootSet allRoots = std::move(*mergedOpt);
#ifndef NDEBUG
    std::cerr << "[CDCAC] allRoots=" << allRoots.numRoots() << std::endl;
    for (int i = 0; i < allRoots.numRoots(); ++i) {
        const auto& r = allRoots.roots[i];
        if (r.isRational()) {
            std::cerr << "[CDCAC] root[" << i << "] rational=" << r.rational.get_d() << std::endl;
        } else {
            std::cerr << "[CDCAC] root[" << i << "] lower=" << r.root.lower.get_d()
                      << " upper=" << r.root.upper.get_d() << std::endl;
        }
    }
#endif

    // 3. Helper: test a sample and recurse to deeper levels
    auto testAndRecurse = [&](const RealAlg& sample) -> CdcacResult {
        ++gCellsTested;
        RealAlg sampleWithOrigin = sample;
        if (sampleWithOrigin.isAlgebraic()) {
            // V2-6: populate RootOrigin for algebraic samples
            RootOrigin origin;
            origin.squarefreeDefiningPoly = sampleWithOrigin.root.definingPoly;
            origin.mainVar = var;
            origin.level = k;
            origin.rootIndex = sampleWithOrigin.root.rootIndex;
            sampleWithOrigin.root.origins.push_back(std::move(origin));
        }
        prefix.push(var, sampleWithOrigin);

        // FORWARD-PRUNE — kills the cell Cartesian-product explosion. A constraint
        // fully determined at this level (all its vars assigned) has a fixed value
        // INDEPENDENT of the deeper variables; if it is definitely violated, no
        // completion satisfies it, so the whole subtree is infeasible and we
        // synthesize the leaf conflict instead of descending.
        //
        // SOUND ON ANY PREFIX (rational OR algebraic) — Task #10 completeness fix.
        // signAt is sound: it returns the true sign (interval arithmetic that strictly
        // excludes 0, else exact libpoly sgn) or Unknown, and we PRUNE ONLY on a
        // definite sign (Unknown is skipped). A fully-determined constraint does not
        // depend on the deeper delineation, so a definite violation rules out the whole
        // subtree regardless of that delineation's completeness; and if THIS level's
        // boundary is incomplete (levelBoundaryComplete=false ⇒ unsatTrustworthy_=false
        // + per-cell cert incomplete) the gate downgrades any resulting UNSAT to
        // Unknown. The earlier rational-only restriction guarded against a then-unsound
        // signAt over algebraic points (Geogebra IsoRightTriangle-Bottema1_17b, z3=sat);
        // the exact interval-first signAt fixed that root cause, so the restriction is
        // removed. No SAT is lost (the prune fires only on a genuinely infeasible
        // subtree) and no UNSAT is lost (an incomplete level taints prune and descent
        // identically).
        CdcacResult childRes;
        {
            std::vector<std::pair<size_t, Sign>> fwViolated;
            // Iterate ONLY the constraints newly determined at this level (deepest var ==
            // varOrder[k]); constraintsAtLevel precomputes this so we no longer rebuild an
            // `assigned` set + rescan every constraint on each cell. Equivalent: ci in this
            // set ⟺ the old (hasVar==(deepest var is var) && allAssigned) test passed.
            for (size_t ci : constraintsAtLevel(static_cast<size_t>(k), input)) {
                Sign s = algebra_->signAt(input.constraints[ci].poly, prefix);
                if (s == Sign::Unknown) continue;        // inconclusive — cannot prune
                if (!relationHolds(s, input.constraints[ci].rel))
                    fwViolated.emplace_back(ci, s);
            }
            // intervalFpViolation now carries algebraic prefix coords as their isolating
            // interval, so it contributes a sound partial-prune over algebraic prefixes
            // too (deep tower levels), not just fully-rational ones. The A-type single-
            // constraint violation it returns is exact (the box ⊇ the true point, so a
            // strict box sign IS the point's sign), making makeLeafConflictResult valid —
            // same as the signAt forward-prune above.
            std::optional<std::pair<size_t, Sign>> ivViol;
            if (fwViolated.empty())
                ivViol = intervalFpViolation(prefix, input);   // partially-determined
            if (!fwViolated.empty())
                childRes = makeLeafConflictResult(fwViolated, input);
            else if (ivViol)
                childRes = makeLeafConflictResult({*ivViol}, input);
            else
                childRes = solveLevel(k + 1, prefix, input);
        }

        prefix.pop();
        if (childRes.status == CdcacStatus::Sat && childRes.model) {
            childRes.model->varOrder.insert(childRes.model->varOrder.begin(), var);
            childRes.model->values.insert(childRes.model->values.begin(), sampleWithOrigin);
        }
        return childRes;
    };

    std::vector<CertifiedCell> certifiedCells;

    // A3 (widening): widen a conflict cell to the REASON-PROJECTION roots — the level polys
    // derived only from the conflict's reason constraints (A2) — instead of all roots, so the
    // cell spans the non-reason-root sectors where the same conflict still holds. Returns the
    // widened root set, or nullopt to fall back to allRoots. SOUND when the conflict's reason
    // set is COMPLETE: between consecutive reason-projection roots the reason constraints'
    // delineation is invariant, so the deeper conflict holds throughout the wider interval.
    auto widenRoots = [&](const CdcacResult& cr) -> std::optional<RootSet> {
        if (!cr.unsat || k < 0 || k >= static_cast<int>(levelPolyIds_.size())) return std::nullopt;
        const std::vector<int> reasonCidx = reasonConstraintIndices(cr.unsat->reasons, input);
        if (reasonCidx.empty()) return std::nullopt;
        // SOUNDNESS GATE: only widen when EVERY reason constraint is FULLY DETERMINED at
        // level k (all its variables are among levels 0..k = prefix ∪ {var}). Then the
        // conflict is a genuine level-k LEAF — those constraints are definitely violated
        // here with NO deeper-variable dependence, so the recorded reasons are RELIABLE
        // and the reason-projection roots truly bound the conflict. A DEEPER conflict
        // (a reason still containing an unassigned var) has UNRELIABLE reasons — the
        // recorded set is a subset of the true conflict support — and widening on it
        // dropped a SAT in test_cdcac_sat_first. Restricting to fully-determined reasons
        // makes the widening sound (a fully-determined constraint's sign is invariant
        // exactly between its own roots, which the reason-projection captures).
        {
            std::unordered_set<VarId> determined(prefix.varOrder.begin(), prefix.varOrder.end());
            determined.insert(var);
            for (int ci : reasonCidx) {
                for (VarId v : constraintVars(static_cast<size_t>(ci), input))
                    if (!determined.count(v)) return std::nullopt;   // deeper var ⇒ not a leaf ⇒ no widen
            }
        }
        const std::vector<PolyId> reasonProj =
            reasonProjectionSubset(polyOrigins_, levelPolyIds_[static_cast<size_t>(k)], reasonCidx);
        if (reasonProj.empty() || reasonProj.size() >= levelPolyIds_[static_cast<size_t>(k)].size())
            return std::nullopt;                       // not a strict subset → no widening benefit
        std::unordered_set<PolyId> rp(reasonProj.begin(), reasonProj.end());
        std::vector<RootSet> filtered;
        for (size_t i = 0; i < rootSets.size() && i < rootSetPolyIds.size(); ++i)
            if (rp.count(rootSetPolyIds[i])) filtered.push_back(rootSets[i]);   // copy (rootSets reused)
        if (filtered.empty()) return std::nullopt;
        auto m = mergeRoots(filtered);
        if (!m) return std::nullopt;
        return m;                                      // widened reason-projection root set
    };
    auto buildCellW = [&](const RealAlg& s, CdcacResult& cr) -> BuildCellResult {
        std::optional<RootSet> wr = widenRoots(cr);
        return buildConflictCell(k, s, cr, input, wr ? *wr : allRoots, levelBoundaryComplete);
    };
    // A4: a sample STRICTLY inside an already-recorded conflict cell is in a proven-
    // infeasible region. Only fully-determined leaf cells are widened (the gate above), and
    // a widened cell is bounded by its reason constraints' own roots ⊆ all-roots, so no
    // in-between root cuts a sector ⇒ sample-in-cell ⇒ sector ⊆ cell ⇒ covered. Skip its
    // recursion + cell (the existing cell keeps the covering complete). Conservative:
    // STRICT '<' and an Unknown algebraic comparison ⇒ NOT covered.
    auto coveredByRecorded = [&](const RealAlg& s) -> bool {
        for (const auto& cc : certifiedCells) {
            const Cell& cl = cc.cell;
            const bool loOk = (cl.lower.kind == Bound::Kind::NegInf) ||
                              (algebra_->compareRealAlg(cl.lower.value, s) == CompareResult::Less);
            if (!loOk) continue;
            const bool hiOk = (cl.upper.kind == Bound::Kind::PosInf) ||
                              (algebra_->compareRealAlg(s, cl.upper.value) == CompareResult::Less);
            if (hiOk) return true;
        }
        return false;
    };

    // 4. Generate and test cells
    if (allRoots.roots.empty()) {
        if (uniPolys.empty() && !projectionSucceeded) {
            // No local constraints at all for this variable
            mpq_class defaultSample(0);
            if (input.seed && input.seed->values.count(var)) {
                defaultSample = input.seed->values.at(var);
            }
            std::cerr << "[CDCAC] no local polys, trying default sample=" << defaultSample.get_d() << std::endl;
            RealAlg sample = RealAlg::fromRational(defaultSample);
            CdcacResult res = testAndRecurse(sample);
            std::cerr << "[CDCAC]   default sample result=" << (int)res.status << std::endl;
            if (res.status == CdcacStatus::Sat) return res;
            if (res.status == CdcacStatus::Unknown) return res;
            // Unsat without cells: cannot construct covering in P2a (no projection)
            return CdcacResult::mkUnknown(CdcacUnknownReason::CoveringDidNotGrow);
        }

        // Has uniPolys but no roots: entire line is one cell ([H5] full-line).
        // The full-line reason is a COMPLETE proof of irrelevance only when this
        // level's boundary construction was complete (levelBoundaryComplete) —
        // i.e. allRoots.empty() reflects genuine root-freeness, not a dropped or
        // unrecovered poly. If levelBoundaryComplete is false the cert is
        // incomplete anyway, so the legal reason is gated by isComplete().
        RealAlg sample = RealAlg::fromRational(mpq_class(0));
        CdcacResult res = testAndRecurse(sample);
        if (res.status == CdcacStatus::Sat) return res;
        if (res.status == CdcacStatus::Unknown) return res;
        auto bcr = buildConflictCell(k, sample, res, input, allRoots, levelBoundaryComplete,
                                     FullLineReason::CompleteLazardEvaluationNoRoots);
        if (bcr.status == BuildCellStatus::Unknown) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
        }
        certifiedCells.push_back(std::move(*bcr.conflictCell));
    } else {
        // Has roots: sectors + sections
        std::optional<RealAlg> prevRoot;

        for (size_t i = 0; i < allRoots.roots.size(); ++i) {
            const RealAlg& root = allRoots.roots[i];
            mpq_class rootVal = root.isRational() ? root.rational : root.root.lower;
            mpq_class rootUpper = root.isRational() ? root.rational : root.root.upper;

            // Sector before this root
            if (prevRoot) {
                mpq_class sectorLo = prevRoot->isRational() ? prevRoot->rational : prevRoot->root.upper;
                mpq_class sectorHi = rootVal;
                if (sectorLo < sectorHi) {
                    mpq_class sampleQ = pickRationalSample(sectorLo, sectorHi);
                    RealAlg sample = RealAlg::fromRational(sampleQ);
                    // BOX-ICP SECTOR PRUNE: if box consistency proves a SUPERSET of
                    // this sector cell — [prevRoot.lower, root.upper] ⊇ (prevRoot,root)
                    // — infeasible, the cell is a sound conflict; synthesize it without
                    // descending the exponential grid below. Rational prefix only.
                    if (!coveredByRecorded(sample)) {   // A4: skip a sector already covered by a widened leaf cell
                    CdcacResult res;
                    bool prefRat = true;
                    for (const auto& pv : prefix.values) if (!pv.isRational()) { prefRat = false; break; }
                    std::optional<std::pair<size_t, Sign>> sv;
                    if (prefRat) {
                        mpq_class boxLo = prevRoot->isRational() ? prevRoot->rational : prevRoot->root.lower;
                        sv = boxSectorViolation(prefix, var, boxLo, rootUpper, input);
                    }
                    if (sv) res = makeLeafConflictResult({*sv}, input);
                    else    res = testAndRecurse(sample);
                    if (res.status == CdcacStatus::Sat) return res;
                    if (res.status == CdcacStatus::Unknown) return res;
                    auto bcr = buildCellW(sample, res);
                    if (bcr.status == BuildCellStatus::Unknown) {
                        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                    }
                    certifiedCells.push_back(std::move(*bcr.conflictCell));
                    }
                }
            } else {
                // First sector: (-inf, r0)
                mpq_class sectorHi = rootVal;
                bool firstConflictRecorded = false;
                CertifiedCell firstConflictCell;
                for (int attempt = 0; attempt < 3; ++attempt) {
                    // attempt 0: z3's simplest value in (−∞, r0) — 0 if it lies inside,
                    // else the integer closest to 0 (the common witness location). Later
                    // attempts march away from the root as before.
                    mpq_class sampleQ = (attempt == 0) ? simplestBelow(sectorHi)
                                                       : (sectorHi - (attempt + 1));
                    RealAlg sample = RealAlg::fromRational(sampleQ);
                    CdcacResult res = testAndRecurse(sample);
                    if (res.status == CdcacStatus::Sat) return res;
                    if (res.status == CdcacStatus::Unknown) return res;
                    if (!firstConflictRecorded) {
                        auto bcr = buildCellW(sample, res);
                        if (bcr.status == BuildCellStatus::Unknown) {
                            return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                        }
                        firstConflictCell = std::move(*bcr.conflictCell);
                        firstConflictRecorded = true;
                        // A conflict cell always contains its own sample. The first sector's
                        // probes march MORE NEGATIVE (sectorHi-1 > -2 > -3); if this cell is
                        // unbounded below (lower=-inf) it covers (-inf, sample] ⊇ every
                        // remaining probe, so those samples sit inside a proven-infeasible
                        // cell and their subtrees are GUARANTEED unsat — not a SAT chance.
                        // Stop probing (sound + complete: the recorded cell already covers
                        // the rest of the sector). Kills 2/3 of the redundant recursion on
                        // the unbounded sector whenever the conflict is robust below.
                        if (firstConflictCell.cell.lower.isNegInf()) break;
                    }
                }
                if (firstConflictRecorded) {
                    certifiedCells.push_back(std::move(firstConflictCell));
                }
            }

            // Section at this root
            {
                // BOX-ICP SECTION PRUNE: a section is the single point var = root.
                // For a RATIONAL root (exact) with a rational prefix, pin var to the
                // degenerate interval [root,root] and box-check: if infeasible the
                // section's subtree is infeasible, so skip its descent (the point cell
                // is sound but contributes nothing to coverage — sectors cover).
                // A4: a root STRICTLY inside a recorded widened leaf cell is in a proven-
                // infeasible region, so skip it — sound, and sections don't affect coverage.
                if (!coveredByRecorded(root)) {
                CdcacResult res;
                std::optional<std::pair<size_t, Sign>> sv;
                if (root.isRational()) {
                    bool prefRat = true;
                    for (const auto& pv : prefix.values) if (!pv.isRational()) { prefRat = false; break; }
                    if (prefRat) sv = boxSectorViolation(prefix, var, root.rational, root.rational, input);
                }
                if (sv) res = makeLeafConflictResult({*sv}, input);
                else    res = testAndRecurse(root);
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                auto bcr = buildCellW(root, res);
                if (bcr.status == BuildCellStatus::Unknown) {
                    return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                }
                certifiedCells.push_back(std::move(*bcr.conflictCell));
                }
            }

            prevRoot = root;
        }

        // Final sector (lastRoot, +inf)
        if (prevRoot) {
            mpq_class sectorLo = prevRoot->isRational() ? prevRoot->rational : prevRoot->root.upper;
            bool firstConflictRecorded = false;
            CertifiedCell firstConflictCell;
            // Try up to 3 samples in the infinite sector before declaring unsat
            for (int attempt = 0; attempt < 3; ++attempt) {
                // attempt 0: z3's simplest value in (lastRoot, +∞) — 0 if it lies inside,
                // else the integer closest to 0.
                mpq_class sampleQ = (attempt == 0) ? simplestAbove(sectorLo)
                                                   : (sectorLo + (attempt + 1));
                RealAlg sample = RealAlg::fromRational(sampleQ);
                CdcacResult res = testAndRecurse(sample);
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                if (!firstConflictRecorded) {
                    auto bcr = buildCellW(sample, res);
                    if (bcr.status == BuildCellStatus::Unknown) {
                        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                    }
                    firstConflictCell = std::move(*bcr.conflictCell);
                    firstConflictRecorded = true;
                    // Symmetric to the first sector: the final sector's probes march MORE
                    // POSITIVE (sectorLo+1 < +2 < +3); if this conflict cell is unbounded
                    // above (upper=+inf) it covers [sample, +inf) ⊇ every remaining probe,
                    // so they sit inside a proven-infeasible cell — guaranteed unsat, not a
                    // SAT chance. Stop probing (sound + complete).
                    if (firstConflictCell.cell.upper.isPosInf()) break;
                }
            }
            if (firstConflictRecorded) {
                certifiedCells.push_back(std::move(firstConflictCell));
            }
        }
    }

    // 5. Build covering and check (copy cells from certifiedCells for legacy Covering)
    Covering cover;
    cover.var = var;
    for (const auto& cc : certifiedCells) {
        cover.cells.push_back(cc.cell);  // copy
    }

#ifndef NDEBUG
    std::cerr << "[CDCAC] final cells=" << cover.cells.size() << std::endl;
#endif
    CoverageResult cov = CoveringManager::coversAllLine(algebra_, cover);
    if (cov == CoverageResult::DoesNotCover) {
        return CdcacResult::mkUnknown(CdcacUnknownReason::InternalInvariantViolation);
    }
    if (cov == CoverageResult::Unknown) {
        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
    }

    // PROOF-CARRYING GATE: the cells geometrically cover the line, but this is
    // a sound UNSAT only if the projection closure underpinning every level's
    // boundaries was complete (no degeneracy / budget / uncertified
    // specialization). Otherwise the covering may over-generalize a deeper
    // conflict — report Unknown rather than a possibly-false UNSAT.
    //
    // FAIL-SAFE per-cell gate: the per-solve `unsatTrustworthy_` is dropped by
    // ANY incomplete step anywhere in the solve tree — including exploratory
    // branches that never enter THIS covering — flooring recoverable UNSATs to
    // Unknown. So additionally trust this covering's UNSAT when (Lazard mode AND
    // the gate is enabled AND) every cell in it carries a COMPLETE
    // LazardCellCertificate, recursively through each cell's child covering.
    // This is strictly >= the per-solve gate (can only turn Unknown→UNSAT,
    // never the reverse) and leaves the Collins / non-Lazard path byte-identical.
    bool perCellTrusted = false;
    if (!unsatTrustworthy_ && lazardModeLevel && lazardCellCertEnabled_) {
        perCellTrusted = !certifiedCells.empty();
        for (const auto& cc : certifiedCells) {
            if (!cc.lazardCert || !cc.lazardCert->isComplete()) { perCellTrusted = false; break; }
            if (cc.certificate.childCoverCert &&
                !coveringCellsAllComplete(*cc.certificate.childCoverCert)) {
                perCellTrusted = false;
                break;
            }
        }
        if (perCellTrusted && std::getenv("XOLVER_NRA_LAZARD_DIAG"))
            std::cerr << "[LAZVAL] per-cell gate RECOVERED UNSAT at level k=" << k
                      << " cells=" << certifiedCells.size() << std::endl;
    }
    if (!unsatTrustworthy_ && !perCellTrusted) {
        return CdcacResult::mkUnknown(CdcacUnknownReason::ProjectionClosureIncomplete);
    }

    auto reasons = ReasonManager::minimize(cover);
    CdcacResult result = CdcacResult::mkUnsat(std::move(cover), std::move(reasons));

    // V3: Build CoveringCertificate
    CoveringCertificate coverCert;
    coverCert.level = k;
    coverCert.var = var;
    for (auto& cc : certifiedCells) {
        coverCert.cells.push_back(std::move(cc));
    }

    // V3: Build CoverageCertificate
    CoverageCertificate coverage;
    coverage.level = k;
    coverage.var = var;
    coverage.coversWholeFiber = true;
    for (size_t i = 0; i < coverCert.cells.size(); ++i) {
        coverage.orderedCells.push_back(cellToFiberCoverage(coverCert.cells[i].cell, i));
    }
    coverCert.coverage = std::move(coverage);

    // V3: Validate certificate (debug build only — catches implementation bugs)
#ifndef NDEBUG
    CellCertificateValidator validator;
    auto valRes = validator.validateCovering(coverCert, algebra_);
    if (valRes.status != ValidationStatus::Valid) {
        std::cerr << "[CDCAC] Certificate validation FAILED: reason=" << static_cast<int>(valRes.reason) << std::endl;
        // Do not abort — validation failure is a bug, but return the result anyway
        // to avoid breaking solver on validator edge cases.
    } else {
        std::cerr << "[CDCAC] Certificate validation OK" << std::endl;
    }
#endif

    result.coveringCert = std::move(coverCert);

    return result;
}

CdcacResult CdcacCore::checkFullSample(const SamplePoint& sample, const CdcacInput& input) {
    std::vector<std::pair<size_t, Sign>> violated;
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        const auto& c = input.constraints[ci];
#ifndef NDEBUG
        std::cerr << "[CDCAC-FULL] poly=" << kernel_->toString(c.poly)
                  << " rel=" << (int)c.rel
                  << " sampleVars=" << sample.numVars() << std::endl;
#endif
        Sign sign = algebra_->signAt(c.poly, sample);
#ifndef NDEBUG
        std::cerr << "[CDCAC-FULL]   sign=" << (int)sign << std::endl;
#endif
        if (sign == Sign::Unknown) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::SignEvaluationInconclusive);
        }
        if (!relationHolds(sign, c.rel)) {
            violated.emplace_back(ci, sign);
        }
    }
    if (!violated.empty()) {
        return makeLeafConflictResult(violated, input);
    }
    return CdcacResult::mkSat(sample);
}

// Build the leaf-style UNSAT result for a set of (constraint-index, definite-sign)
// violations. Shared by checkFullSample (full-sample leaf) and solveLevel's
// forward-prune. The cell is FullLine; its LazardCellCertificate is COMPLETE
// because every listed sign was a definite signAt result (no Unknown).
CdcacResult CdcacCore::makeLeafConflictResult(
    const std::vector<std::pair<size_t, Sign>>& violated, const CdcacInput& input) {
    std::vector<SatLit> conflictLits;
    std::vector<AtomCondition> atomConditions;
    std::vector<CertificateReasonLit> certReasons;
    for (const auto& [ci, sign] : violated) {
        const auto& c = input.constraints[ci];
        conflictLits.push_back(c.reason);

        AtomCondition ac;
        ac.atom = NullAtom;
        ac.poly = c.poly;
        ac.rel = c.rel;
        ac.allowedSigns = signSetFromRelation(c.rel);
        ac.invariantSigns = signToAtomSignSet(sign);
        ac.isConstant = kernel_->isConstant(c.poly);
        atomConditions.push_back(std::move(ac));

        CertificateReasonLit crl;
        crl.lit = c.reason;
        crl.atom = NullAtom;
        crl.polarity = true;
        crl.normalized = {c.poly, c.rel};
        certReasons.push_back(std::move(crl));
    }
    {
        VarId var = input.varOrder.empty() ? NullVar : input.varOrder[0];
        int level = static_cast<int>(input.varOrder.size());

        // Build Cell (for legacy Covering)
        Cell cellForCover;
        cellForCover.var = var;
        cellForCover.kind = CellKind::FullLine;
        cellForCover.lower = Bound::negInf();
        cellForCover.upper = Bound::posInf();
        cellForCover.reasons = conflictLits;

        // Build CellCertificate
        CellCertificate cert;
        cert.kind = CellCertificateKind::FullLineViolation;
        cert.level = level;
        cert.var = var;
        cert.cell = cellForCover;  // copy
        cert.atomConditions = std::move(atomConditions);
        cert.reasons = std::move(certReasons);

        // Build legacy Covering
        Covering cover;
        cover.var = var;
        cover.cells.push_back(std::move(cellForCover));
        auto reasons = ReasonManager::minimize(cover);

        CdcacResult result = CdcacResult::mkUnsat(std::move(cover), std::move(reasons));

        // Build V3 CoveringCertificate
        CoveringCertificate coverCert;
        coverCert.level = level;
        coverCert.var = var;
        // Note: cover.cells[0] may have been moved, so copy from the original cell
        Cell cellCopy = cellForCover;  // copy original cell before it was moved
        CertifiedCell leafCC{std::move(cellCopy), std::move(cert), std::nullopt};
        // FAIL-SAFE per-cell gate: a full-sample (all vars concrete) conflict is
        // an EXACT point conflict — every constraint's signAt returned a definite
        // sign (else we returned SignEvaluationInconclusive above). So the leaf
        // cell is complete by construction. Mark it so the recursive per-cell
        // gate can trust coverings rooted at deeper levels. (Mode-agnostic but
        // only READ in Lazard mode.)
        {
            LazardCellCertificate lc;
            lc.closureId = lazardClosure_.closureId();
            lc.prefixCellId = 0;
            lc.closureComplete = closureComplete_;
            lc.prefixComplete = true;      // no deeper level — leaf
            lc.valuationComplete = true;   // exact concrete evaluation
            lc.rootIsolationComplete = true;
            lc.rootMergeComplete = true;
            // Leaf is the full-sample point conflict (not a full-line proof of
            // irrelevance); no fullLineReason ⇒ generic complete cell.
            leafCC.lazardCert = std::move(lc);
        }
        coverCert.cells.push_back(std::move(leafCC));

        // V3: Build CoverageCertificate
        CoverageCertificate coverage;
        coverage.level = level;
        coverage.var = var;
        coverage.coversWholeFiber = true;
        coverage.orderedCells.push_back(cellToFiberCoverage(coverCert.cells[0].cell, 0));
        coverCert.coverage = std::move(coverage);

#ifndef NDEBUG
        CellCertificateValidator validator;
        auto valRes = validator.validateCovering(coverCert, algebra_);
        if (valRes.status != ValidationStatus::Valid) {
            std::cerr << "[CDCAC] Leaf certificate validation FAILED: reason=" << static_cast<int>(valRes.reason) << std::endl;
        } else {
            std::cerr << "[CDCAC] Leaf certificate validation OK" << std::endl;
        }
#endif

        result.coveringCert = std::move(coverCert);

        return result;
    }
}

// --- nlsat-engine STEP A: SAT-only sample-first model search --------------------
// Rational cell-representative candidates for `var` at the current prefix. Lazy
// single-cell delineation by the real roots of each SAFE constraint poly that is
// univariate in `var` here (satSafe_ skips the libpoly-crash class; signAt at the
// leaf still validates all). Algebraic roots contribute a rational inside their
// isolating interval — checkFullSample exact-validates the full point, so an
// approximate boundary only misses a model, never admits a false one.
// Bit-length of a rational = max bit-size of |num| and den. Used to discard
// astronomically large sample candidates (additive search restriction).
static long mpqBitLen(const mpq_class& q) {
    long a = (q.get_num() == 0) ? 0
             : static_cast<long>(mpz_sizeinbase(q.get_num().get_mpz_t(), 2));
    long b = static_cast<long>(mpz_sizeinbase(q.get_den().get_mpz_t(), 2));
    return a > b ? a : b;
}

// Simplest rational strictly inside the open interval (lo, hi), lo < hi: an
// integer closest to 0 if one fits, else the smallest-denominator dyadic k/2^j.
// This is de Moura's NLSAT cell-sample rule — it keeps the chosen value SMALL,
// unlike an interval midpoint whose numerator/denominator compound across the
// recursion until libpoly's interval power blows up (the matrix-1-all SIGSEGV).
static mpq_class simplestRationalIn(const mpq_class& lo, const mpq_class& hi) {
    if (lo < 0 && hi > 0) return mpq_class(0);                 // 0 is simplest of all
    // Smallest integer strictly > lo, largest integer strictly < hi.
    mpz_class flo; mpz_fdiv_q(flo.get_mpz_t(), lo.get_num().get_mpz_t(), lo.get_den().get_mpz_t());
    mpz_class nlo = flo + 1;
    mpz_class chi; mpz_cdiv_q(chi.get_mpz_t(), hi.get_num().get_mpz_t(), hi.get_den().get_mpz_t());
    mpz_class nhi = chi - 1;
    if (nlo <= nhi)                                            // an integer fits
        return mpq_class(lo >= 0 ? nlo : nhi);                // closest to 0
    for (int j = 1; j <= 256; ++j) {                          // smallest-denominator dyadic
        mpz_class den = mpz_class(1) << j;
        mpq_class loS = lo * den;
        mpz_class fk; mpz_fdiv_q(fk.get_mpz_t(), loS.get_num().get_mpz_t(), loS.get_den().get_mpz_t());
        mpq_class cand(fk + 1, den); cand.canonicalize();
        if (cand < hi) return cand;
    }
    mpq_class mid = (lo + hi) / 2;                            // unreachable fallback
    return mid;
}

// EXACT sign (−1/0/+1) of `rp` at a rational assignment (missing var ⇒ 0), by
// pure-mpq term-sum Σ coeff·Π baseᵉ. NEVER routes through libpoly
// coefficient_sgn / rational_interval_pow (the OOM-SIGSEGV path) — this is the
// real, principled sign by exact rational arithmetic, and with sampled values
// bounded (simplestRationalIn + magnitude filter) the accumulator stays small.
static int exactSignAt(const RationalPolynomial& rp,
                       const std::unordered_map<VarId, mpq_class>& asg) {
    mpq_class acc(0);
    for (const auto& [key, coeff] : rp.terms()) {
        mpq_class term = coeff;
        for (const auto& [v, e] : key) {
            auto it = asg.find(v);
            mpq_class base = (it != asg.end()) ? it->second : mpq_class(0);
            long ee = static_cast<long>(e);
            for (long i = 0; i < ee && sgn(term) != 0; ++i) term *= base;
        }
        acc += term;
    }
    return sgn(acc);
}

std::vector<mpq_class> CdcacCore::satSampleCandidates(VarId var, const SamplePoint& prefix,
                                                      const CdcacInput& input) {
    std::vector<mpq_class> roots;
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        if (ci < satSafe_.size() && !satSafe_[ci]) continue;   // skip libpoly-crash-class polys
        const auto& c = input.constraints[ci];
        if (kernel_->isConstant(c.poly)) continue;
        UniPolyId up = algebra_->specializeToUnivariate(c.poly, prefix, var);
        if (up == NullUniPolyId) continue;                     // free higher vars / no `var` here
        RootSet rs = algebra_->isolateRealRoots(up);
        if (rs.crashOccurred) continue;                        // firewall-declined → sampling handles it
        for (const auto& r : rs.roots)
            roots.push_back(r.isRational() ? r.rational
                                           : (r.root.lower + r.root.upper) / 2);
    }
    std::sort(roots.begin(), roots.end());
    roots.erase(std::unique(roots.begin(), roots.end()), roots.end());

    std::vector<mpq_class> cands;
    // Universal small-integer fallbacks: always within the magnitude bound, so a
    // small-coordinate model is reachable even when every root is astronomically
    // large (then the structured cell samples below are all filtered out).
    for (long v : {0, 1, -1, 2, -2, 3, -3}) cands.push_back(mpq_class(v));
    if (!roots.empty()) {
        // Simple integer just below the first / above the last root.
        mpz_class f; mpz_fdiv_q(f.get_mpz_t(), roots.front().get_num().get_mpz_t(),
                                roots.front().get_den().get_mpz_t());
        cands.push_back(mpq_class(f - 1));
        mpz_class g; mpz_cdiv_q(g.get_mpz_t(), roots.back().get_num().get_mpz_t(),
                                roots.back().get_den().get_mpz_t());
        cands.push_back(mpq_class(g + 1));
        for (size_t i = 0; i < roots.size(); ++i) {
            cands.push_back(roots[i]);                          // the "= root" cell
            if (i + 1 < roots.size() && roots[i] < roots[i + 1])
                cands.push_back(simplestRationalIn(roots[i], roots[i + 1]));  // open-cell rep
        }
    }
    // Magnitude filter: discard candidates beyond the bound (keeps every
    // downstream specialization/evaluation bounded ⇒ crash-free). Additive only —
    // the complete projection engine still runs on fall-through.
    std::vector<mpq_class> out;
    for (auto& q : cands)
        if (mpqBitLen(q) <= satSampleMaxBits_) out.push_back(std::move(q));
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    // Step-B search bias: try the SIMPLEST candidates first — smallest |value|,
    // ties by smaller denominator then value. Real SAT models cluster at small
    // rationals (e.g. the matrix-* z3 models are {0,1,2,3,1/2,1/8}); plain
    // ascending order wastes the DFS budget on large-negative samples first.
    // Pure reordering of the exploration — SAT is still returned only on a
    // leaf-exact-validated full point, so this is soundness-neutral (it can only
    // change WHICH model / how fast one is found, never correctness).
    std::stable_sort(out.begin(), out.end(), [](const mpq_class& a, const mpq_class& b) {
        mpq_class aa = abs(a), bb = abs(b);
        if (aa != bb) return aa < bb;
        if (a.get_den() != b.get_den()) return a.get_den() < b.get_den();
        return a < b;
    });
    return out;
}

// Maps an exact rational sign (−1/0/+1 from exactSignAt) against a relation.
static inline bool satRelHolds(int s, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return s == 0;
        case Relation::Neq: return s != 0;
        case Relation::Lt:  return s < 0;
        case Relation::Leq: return s <= 0;
        case Relation::Gt:  return s > 0;
        case Relation::Geq: return s >= 0;
    }
    return false;
}

// --- nlsat-engine INCREMENT 4: ALGEBRAIC-model SAT-first ------------------------
// Candidate set for `var` = the full rational candidate set (proven logic, wrapped
// as RealAlg) PLUS the ACTUAL algebraic roots (the irrational roots themselves, not
// their rational midpoints). The algebraic roots are what let the search assign,
// e.g., v=√2 to satisfy v^2=2 exactly — unreachable by any rational sample.
std::vector<RealAlg> CdcacCore::satSampleCandidatesAlg(VarId var, const SamplePoint& prefix,
                                                       const CdcacInput& input) {
    // Precompute the assigned set so we only attempt the (expensive) algebraic-prefix
    // root isolation on a constraint that is ACTUALLY univariate in `var` given the
    // prefix — i.e. every other variable of the constraint is already assigned. Without
    // this guard every node ran ~|constraints| resultant-Norm / Lazard-tower calls
    // (most unsupported after heavy work), which alone exhausted the budget on the towers.
    std::unordered_set<VarId> assigned(prefix.varOrder.begin(), prefix.varOrder.end());
    // TOWER-DEPTH CAP: the multi-algebraic Lazard-tower root isolation (resultant Norm
    // over the field tower) cost explodes with the number of algebraic prefix
    // coordinates — a single deep-tower call can run past the wall budget (the search
    // can't interrupt mid-call). Beyond the cap we skip the tower path, which bounds the
    // per-node cost; the deep degree-8-12 RegPolygon towers are out of reach anyway, and
    // the shallow ones (≤cap algebraic coords) that DO solve are preserved.
    long algPrefixCount = 0;
    for (const auto& v : prefix.values) if (!v.isRational()) ++algPrefixCount;
    static const long kTowerCap = [] {
        int v = env::paramInt("XOLVER_NRA_CAC_SAT_FIRST_TOWER_CAP", 4);
        return v > 0 ? static_cast<long>(v) : 4L;
    }();
    auto univariateInVar = [&](PolyId poly) -> bool {
        bool varPresent = false;
        for (const auto& vn : kernel_->variables(poly)) {
            VarId v = kernel_->getOrCreateVar(vn);
            if (v == var) { varPresent = true; continue; }
            if (!assigned.count(v)) return false;   // another unassigned var remains
        }
        return varPresent;
    };
    // Roots of `poly` in `var` at the (possibly algebraic) point.
    auto rootsInVar = [&](PolyId poly, std::vector<RealAlg>& out) {
        UniPolyId up = algebra_->specializeToUnivariate(poly, prefix, var);
        if (up != NullUniPolyId) {
            RootSet rs = algebra_->isolateRealRoots(up);
            if (!rs.crashOccurred) for (const auto& r : rs.roots) out.push_back(r);
            return;
        }
        if (!univariateInVar(poly)) return;
        // (1) Resultant-Norm / Lazard-tower for SHALLOW towers (within the cap).
        if (algPrefixCount <= kTowerCap) {
            bool supNorm = false, supTower = false;
            RootSet rs = algebra_->isolateRealRootsViaNorm(poly, prefix, var, supNorm);
            if (!supNorm) rs = algebra_->isolateRealRootsViaTower(poly, prefix, var, supTower);
            if ((supNorm || supTower) && !rs.crashOccurred && !rs.roots.empty()) {
                for (const auto& r : rs.roots) out.push_back(r);
                return;
            }
        }
        // (2) DEEP tower: libpoly's native incremental isolation over the PERSISTENT
        // assignment (cost scales with the step degree, not the cumulative tower; the
        // assignment cache keeps lower coords' interval refinements across the descent).
        RootSet rs = algebra_->isolateRealRootsAlgebraic(poly, prefix, var);
        if (!rs.crashOccurred) for (const auto& r : rs.roots) out.push_back(r);
    };
    // DETERMINED variable: if an EQUALITY constraint is univariate in `var` given the
    // prefix, `var` is PINNED to one of that equality's roots — no other value can hold
    // it. Offer ONLY those forced roots (1–2 of them), turning each triangular level
    // into a 1–2-way branch instead of an 8–11-way one over rational fallbacks that the
    // equality immediately falsifies. This is what makes the SAT-first descend a deep
    // RegPolygon tower within budget (the per-node signAt over the tower is expensive).
    std::vector<RealAlg> eqRoots;
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        if (ci < satSafe_.size() && !satSafe_[ci]) continue;
        if (input.constraints[ci].rel != Relation::Eq) continue;
        const PolyId poly = input.constraints[ci].poly;
        if (kernel_->isConstant(poly)) continue;
        rootsInVar(poly, eqRoots);
    }
    // `var` is equality-determined (pickSatFirstVar guarantees it), so ONLY this
    // equality's roots can hold it — return exactly those. Empty (e.g. the tower-depth
    // cap declined a deep isolation) means this branch can't be advanced: the caller
    // backtracks, never wandering over rational samples of an under-determined variable.
    return eqRoots;
}

// Most-constrained-variable pick: prefer an unassigned variable that some EQUALITY
// constraint determines (every OTHER variable of that equality is already assigned, so
// it specializes to a univariate equation whose roots FORCE this variable). Falling
// back to the next unassigned variable in input.varOrder. Turning the static order
// into this triangular order is what lets the algebraic SAT-first descend a multi-level
// tower (RegPolygon) one forced root at a time instead of guessing under-determined
// variables.
VarId CdcacCore::pickSatFirstVar(const SamplePoint& prefix, const CdcacInput& input) {
    std::unordered_set<VarId> assigned(prefix.varOrder.begin(), prefix.varOrder.end());
    // Return the variable an EQUALITY already pins (exactly one unassigned var in it, so
    // it specializes to a univariate equation whose roots force this variable). If NO
    // such variable exists, return NullVar so the algebraic SAT-first BAILS immediately
    // instead of wandering over rational samples of an under-determined coordinate — that
    // fast-bail is what keeps the default-on path at ~0 overhead on non-triangular inputs
    // (meti-tarski / hycomp inequality systems): it only ever does real work on the
    // triangular algebraic-SAT structure it can actually solve.
    for (const auto& c : input.constraints) {
        if (c.rel != Relation::Eq) continue;
        if (kernel_->isConstant(c.poly)) continue;
        VarId only = NullVar; bool multi = false; bool hasVar = false;
        for (const auto& vn : kernel_->variables(c.poly)) {
            VarId v = kernel_->getOrCreateVar(vn);
            hasVar = true;
            if (assigned.count(v)) continue;
            if (only != NullVar) { multi = true; break; }
            only = v;
        }
        if (!multi && hasVar && only != NullVar) return only;   // determined by this equality
    }
    return NullVar;   // no equality-determined variable: bail (fall through to projection)
}

// Algebraic SAT-first recursion. Mirrors trySatSampleFirst but assigns RealAlg
// (possibly algebraic) values and evaluates EVERY sign via algebra_->signAt (the
// libpoly algebraic sign — gated to low-degree systems in solve() for crash-safety).
// Soundness-SAFE: Sat ONLY on a full point where every constraint's signAt gives a
// definite sign satisfying its relation; signAt==Unknown is inconclusive and never
// concludes (forward-check: don't prune; leaf: don't claim a model). Never Unsat.
CdcacResult CdcacCore::trySatSampleFirstAlg(int k, SamplePoint& prefix,
                                            const CdcacInput& input, long& budget) {
    int n = static_cast<int>(input.varOrder.size());
    if (k == n) {
        for (const auto& c : input.constraints) {
            Sign s = algebra_->signAt(c.poly, prefix);
            if (s == Sign::Unknown || !relationHolds(s, c.rel))
                return CdcacResult::mkUnknown(CdcacUnknownReason::None);
        }
        return CdcacResult::mkSat(prefix);   // full algebraic point, all constraints hold
    }
    if (budget <= 0) return CdcacResult::mkUnknown(CdcacUnknownReason::None);
    VarId var = pickSatFirstVar(prefix, input);          // dynamic most-constrained pick
    if (var == NullVar) return CdcacResult::mkUnknown(CdcacUnknownReason::None);
    std::vector<RealAlg> cands = satSampleCandidatesAlg(var, prefix, input);
    std::unordered_set<VarId> assigned;
    for (VarId v : prefix.varOrder) assigned.insert(v);
    assigned.insert(var);
    for (auto& cand : cands) {
        if (budget <= 0) break;
        --budget;
        if (satFirstMs_ > 0 && (budget & 1023) == 0) {
            auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                          std::chrono::steady_clock::now() - satFirstT0_).count();
            if (ms > satFirstMs_) { budget = 0; break; }
        }
        prefix.push(var, cand);
        // Forward-check: only constraints NEWLY fully-determined at THIS level get a
        // signAt. A constraint must (a) contain `var` and (b) have all its vars
        // assigned. The `hasVar` guard is the key: a constraint fully assigned at a
        // SHALLOWER level was already sign-checked the moment its last variable was
        // fixed (and passed — else we pruned then), and its value is independent of
        // `var`, so re-checking it at every candidate of `var` is pure redundant work
        // (an expensive libpoly signAt over an algebraic prefix). Skipping it loses no
        // pruning (it stays satisfied) and no soundness (the k==n leaf re-validates
        // EVERY constraint). Mirrors solveLevel's forward-prune, which already gates on
        // hasVar. (Explicit all-assigned guard avoids relying on signAt's partial
        // behaviour.)
        bool pruned = false;
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            if (ci >= satRp_.size() || !satRp_[ci]) continue;
            bool allAssigned = true, hasVar = false;
            for (VarId v : satRp_[ci]->variables()) {
                if (v == var) hasVar = true;
                if (!assigned.count(v)) { allAssigned = false; break; }
            }
            if (!hasVar || !allAssigned) continue;       // only NEWLY-determined here
            Sign s = algebra_->signAt(input.constraints[ci].poly, prefix);
            if (s == Sign::Unknown) continue;            // inconclusive — don't prune
            if (!relationHolds(s, input.constraints[ci].rel)) { pruned = true; break; }
        }
        // Box-ICP partial-assignment lookahead — "carry the assignment, exclude the
        // impossible regions as you descend" on the DEFAULT (algebraic) SAT-first path.
        // The forward-check above only fires once a constraint is FULLY assigned; box
        // consistency over the partial assignment prunes whole infeasible subtrees far
        // earlier. subtreeBoxInfeasiblePrefix carries the assignment FAITHFULLY (rational
        // coords as exact points, algebraic coords as their isolating interval — a sound
        // tight box) and over-approximates, so an empty box proves the subtree infeasible
        // without ever over-pruning a real model (invariant 1; the k==n leaf still
        // validates every constraint). Skipped at the leaf and when nothing is fixed yet.
        if (!pruned && k + 1 < n && subtreeBoxInfeasiblePrefix(prefix, input))
            pruned = true;
        if (pruned) { prefix.pop(); continue; }
        CdcacResult r = trySatSampleFirstAlg(k + 1, prefix, input, budget);
        prefix.pop();
        if (r.status == CdcacStatus::Sat) return r;
    }
    return CdcacResult::mkUnknown(CdcacUnknownReason::None);
}

// ── M2: box-consistency interval arithmetic (extended reals with ±∞) ──────────
// A sound natural interval extension. Every op over-approximates the true range,
// so a box built by these ops always CONTAINS the feasible projection — the basis
// for proving infeasibility without ever over-pruning a real model.
namespace {
struct Iv {
    bool loInf = false, hiInf = false;   // ±∞ flags; endpoints valid when !flag
    mpq_class lo, hi;
    static Iv all()  { Iv x; x.loInf = x.hiInf = true; return x; }
    static Iv point(const mpq_class& q) { Iv x; x.lo = x.hi = q; return x; }
    bool isAll() const { return loInf && hiInf; }
    bool empty() const { return !loInf && !hiInf && lo > hi; }
};
// extended real: inf=-1 → −∞, 0 → finite val, +1 → +∞
struct XR { int inf; mpq_class val; };
static bool xless(const XR& a, const XR& b) {
    if (a.inf != b.inf) return a.inf < b.inf;
    if (a.inf != 0) return false;            // same ±∞
    return a.val < b.val;
}
static XR xmul(const XR& a, const XR& b) {
    bool az = (a.inf == 0 && sgn(a.val) == 0), bz = (b.inf == 0 && sgn(b.val) == 0);
    if (az || bz) return {0, mpq_class(0)};   // 0 · anything (incl. ±∞) ≡ 0 for a range
    if (a.inf == 0 && b.inf == 0) return {0, a.val * b.val};
    int sa = a.inf != 0 ? a.inf : sgn(a.val);
    int sb = b.inf != 0 ? b.inf : sgn(b.val);
    return {sa * sb, mpq_class(0)};
}
static Iv ivAdd(const Iv& a, const Iv& b) {
    Iv r;
    r.loInf = a.loInf || b.loInf; if (!r.loInf) r.lo = a.lo + b.lo;
    r.hiInf = a.hiInf || b.hiInf; if (!r.hiInf) r.hi = a.hi + b.hi;
    return r;
}
static Iv ivNeg(const Iv& a) {
    Iv r;
    r.loInf = a.hiInf; if (!r.loInf) r.lo = -a.hi;
    r.hiInf = a.loInf; if (!r.hiInf) r.hi = -a.lo;
    return r;
}
static Iv ivMul(const Iv& a, const Iv& b) {
    XR al = a.loInf ? XR{-1, {}} : XR{0, a.lo}, ah = a.hiInf ? XR{1, {}} : XR{0, a.hi};
    XR bl = b.loInf ? XR{-1, {}} : XR{0, b.lo}, bh = b.hiInf ? XR{1, {}} : XR{0, b.hi};
    XR c[4] = {xmul(al, bl), xmul(al, bh), xmul(ah, bl), xmul(ah, bh)};
    XR mn = c[0], mx = c[0];
    for (int i = 1; i < 4; ++i) { if (xless(c[i], mn)) mn = c[i]; if (xless(mx, c[i])) mx = c[i]; }
    if (mn.inf > 0 || mx.inf < 0) return Iv::all();   // degenerate; stay sound
    Iv r;
    r.loInf = (mn.inf < 0); if (!r.loInf) r.lo = mn.val;
    r.hiInf = (mx.inf > 0); if (!r.hiInf) r.hi = mx.val;
    return r;
}
static Iv ivPow(const Iv& a, long e) {
    if (e <= 0) return Iv::point(mpq_class(1));
    Iv r = a;
    for (long i = 1; i < e; ++i) r = ivMul(r, a);
    if ((e % 2) == 0) {                  // even power ≥ 0 — sound tightening even if unbounded
        if (r.loInf || r.lo < 0) { r.loInf = false; r.lo = 0; }
    }
    return r;
}
static Iv ivIntersect(const Iv& a, const Iv& b) {
    Iv r;
    if (a.loInf) { r.loInf = b.loInf; r.lo = b.lo; }
    else if (b.loInf) { r.loInf = false; r.lo = a.lo; }
    else { r.loInf = false; r.lo = (a.lo > b.lo ? a.lo : b.lo); }
    if (a.hiInf) { r.hiInf = b.hiInf; r.hi = b.hi; }
    else if (b.hiInf) { r.hiInf = false; r.hi = a.hi; }
    else { r.hiInf = false; r.hi = (a.hi < b.hi ? a.hi : b.hi); }
    return r;
}
// Reciprocal of an interval that does NOT contain 0 (caller guarantees).
static Iv ivRecip(const Iv& a) {
    // a is strictly positive or strictly negative (0 ∉ a).
    Iv r;
    // new lo = 1/hi, new hi = 1/lo (monotone-decreasing 1/x on each sign side)
    if (a.hiInf) { r.loInf = false; r.lo = 0; }
    else { r.loInf = false; r.lo = mpq_class(1) / a.hi; }
    if (a.loInf) { r.hiInf = false; r.hi = 0; }
    else { r.hiInf = false; r.hi = mpq_class(1) / a.lo; }
    return r;
}
static bool ivExcludesZero(const Iv& a) {
    return (!a.loInf && a.lo > 0) || (!a.hiInf && a.hi < 0);
}
// Can `poly REL 0` hold for SOME value in over-approx range r?
static bool ivRelCanHold(const Iv& r, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return (r.loInf || r.lo <= 0) && (r.hiInf || r.hi >= 0);
        case Relation::Neq: return !(!r.loInf && !r.hiInf && r.lo == 0 && r.hi == 0);
        case Relation::Lt:  return r.loInf || r.lo < 0;
        case Relation::Leq: return r.loInf || r.lo <= 0;
        case Relation::Gt:  return r.hiInf || r.hi > 0;
        case Relation::Geq: return r.hiInf || r.hi >= 0;
    }
    return true;
}
}  // namespace

// Natural interval extension of `rp` over (point vars = pts) × (interval vars = box).
// A var absent from both is unbounded (all()). Over-approximates the true range.
static Iv ivEval(const RationalPolynomial& rp,
                 const std::unordered_map<VarId, mpq_class>& pts,
                 const std::unordered_map<VarId, Iv>& box) {
    Iv acc = Iv::point(mpq_class(0));
    for (const auto& [key, coeff] : rp.terms()) {
        Iv term = Iv::point(coeff);
        for (const auto& [v, e] : key) {
            auto pit = pts.find(v);
            Iv vi;
            if (pit != pts.end()) vi = Iv::point(pit->second);
            else { auto bit = box.find(v); vi = (bit != box.end()) ? bit->second : Iv::all(); }
            term = ivMul(term, ivPow(vi, static_cast<long>(e)));
            if (term.isAll()) break;   // no further tightening possible for this term
        }
        acc = ivAdd(acc, term);
    }
    return acc;
}

// BOUNDED-BIT rational upper bound r ≥ √U for U ≥ 0. EXACT when U is a perfect
// rational square (the common sum-of-squares case, √1=1 ⇒ tight |x|≤1). Otherwise a
// double-derived rational on a fixed 2^-24 grid, bumped until r²≥U — bounded
// numerator/denominator so it never blows up. (An EXACT rational Newton would double
// the bit-size every step → multi-GB OOM; that was the bug.) Sound: r ≥ √U ⇒ [−r,r]
// ⊇ the true v-range, so the box stays an over-approximation.
static mpq_class ratSqrtUpper(const mpq_class& U) {
    if (U <= 0) return mpq_class(0);
    mpz_class p = U.get_num(), q = U.get_den();
    if (mpz_perfect_square_p(p.get_mpz_t()) && mpz_perfect_square_p(q.get_mpz_t())) {
        mpz_class sp, sq;
        mpz_sqrt(sp.get_mpz_t(), p.get_mpz_t());
        mpz_sqrt(sq.get_mpz_t(), q.get_mpz_t());
        mpq_class r(sp, sq); r.canonicalize(); return r;            // exact √U
    }
    const double d = std::sqrt(U.get_d());
    if (!std::isfinite(d) || d <= 0) return U + 1;                  // sound coarse bound (√U ≤ U+1)
    const long G = 1L << 24;
    mpq_class r(static_cast<long>(std::ceil(d * static_cast<double>(G))) + 1, G);  // ≈ √U from above
    r.canonicalize();
    for (int k = 0; k < 64 && r * r < U; ++k) r += mpq_class(1, G); // bump up (bounded, few steps)
    if (r * r < U) return U + 1;                                    // last-resort sound bound
    return r;
}

// Box-consistency HC4 fixpoint. Fills `box` (one Iv per UNASSIGNED var, each an
// over-approximation that always CONTAINS the feasible projection) and returns true iff
// the subtree under `m` is provably infeasible. Shared by M2 (infeasibility pruning)
// and M1 (feasible-cell value selection). Sound by over-approximation throughout.
static bool propagateBox(const std::vector<std::optional<RationalPolynomial>>& satRp,
                         const std::vector<bool>& satSafe,
                         const std::unordered_map<VarId, mpq_class>& m,
                         const CdcacInput& input,
                         std::unordered_map<VarId, Iv>& box,
                         std::optional<std::pair<size_t, Sign>>* aConf = nullptr,
                         const std::unordered_map<VarId, Iv>* seed = nullptr) {
    box.clear();
    for (VarId v : input.varOrder) {
        if (m.count(v)) continue;
        // An unassigned var defaults to (−∞,∞); `seed` lets the caller pin one to a
        // known cell interval (sector) — proving THAT box infeasible proves the whole
        // cell infeasible (sound: box ⊇ feasible projection over the cell).
        box[v] = Iv::all();
        if (seed) { auto it = seed->find(v); if (it != seed->end()) box[v] = it->second; }
    }
    if (box.empty()) return false;   // all vars assigned — the leaf check handles it
    std::vector<size_t> cons;
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        if (ci >= satRp.size() || !satRp[ci]) continue;
        if (ci < satSafe.size() && !satSafe[ci]) continue;
        cons.push_back(ci);
    }
    if (cons.empty()) return false;
    const int kMaxRounds = 16;
    // When a contraction EMPTIES a variable's box, the emptying constraint forced v
    // outside its interval, so that constraint evaluated over the current box is
    // strictly single-signed-violating — exactly the (A)-type reason. Surface it so the
    // covering's intervalFpViolation gets a usable (constraint,sign) and can PRUNE (a
    // contraction-empty otherwise returned with no aConf → was discarded → no prune).
    // Same soundness basis as the (A) check below (only fires when the over-approx range
    // provably excludes 0); the cell interval is still delineation-derived, so blaming a
    // single constraint over the contracted box never widens the cell (no false-UNSAT).
    auto setConf = [&](size_t ci) {
        if (!aConf) return;
        Iv rr = ivEval(*satRp[ci], m, box);
        if (!rr.loInf && rr.lo > 0) *aConf = std::make_pair(ci, Sign::Pos);
        else if (!rr.hiInf && rr.hi < 0) *aConf = std::make_pair(ci, Sign::Neg);
    };
    for (int round = 0; round < kMaxRounds; ++round) {
        bool changed = false;
        // (A) Infeasibility: over-approx range of each constraint must admit the relation.
        for (size_t ci : cons) {
            Iv r = ivEval(*satRp[ci], m, box);
            if (!ivRelCanHold(r, input.constraints[ci].rel)) {
                // Surface a STRICT single-signed conflict (r ⊂ (0,∞) or (−∞,0)) for a
                // clean full-line invariant-sign conflict cell. Over the CONTRACTED box
                // far more constraints are strictly signed than over the raw R^n.
                if (aConf) {
                    if (!r.loInf && r.lo > 0) *aConf = std::make_pair(ci, Sign::Pos);
                    else if (!r.hiInf && r.hi < 0) *aConf = std::make_pair(ci, Sign::Neg);
                }
                return true;
            }
        }
        // (B) Degree-1 contraction: A·v + B rel 0 ⇒ tighten box[v].
        for (size_t ci : cons) {
            const RationalPolynomial& rp = *satRp[ci];
            Relation rel = input.constraints[ci].rel;
            for (auto& [v, ivCur] : box) {
                if (rp.degree(v) != 1) continue;
                std::vector<RationalPolynomial> co = rp.coefficients(v);  // [B, A]
                if (co.size() < 2) continue;
                Iv A = ivEval(co[1], m, box), B = ivEval(co[0], m, box);
                if (!ivExcludesZero(A)) continue;   // sign of A undetermined ⇒ no clean bound
                Iv tight;
                if (rel == Relation::Eq) {
                    tight = ivMul(ivNeg(B), ivRecip(A));        // v = −B/A
                } else if (rel == Relation::Leq || rel == Relation::Lt ||
                           rel == Relation::Geq || rel == Relation::Gt) {
                    // A·v + B rel 0 ⇒ v rel' −B/A (sense flips when A<0).
                    Iv vb = ivMul(ivNeg(B), ivRecip(A));        // the −B/A bound interval
                    bool aPos = (!A.loInf && A.lo > 0);
                    bool lower = (rel == Relation::Geq || rel == Relation::Gt);   // v ≥ … (A>0)
                    if (!aPos) lower = !lower;                  // A<0 flips the inequality
                    tight = Iv::all();
                    if (lower) { tight.loInf = vb.loInf; tight.lo = vb.lo; }   // v ≥ bound
                    else       { tight.hiInf = vb.hiInf; tight.hi = vb.hi; }   // v ≤ bound
                } else {
                    continue;   // Neq: no contraction
                }
                Iv nv = ivIntersect(ivCur, tight);
                if (nv.empty()) { setConf(ci); return true; }   // no feasible v ⇒ infeasible
                if (nv.loInf != ivCur.loInf || nv.hiInf != ivCur.hiInf ||
                    (!nv.loInf && nv.lo != ivCur.lo) || (!nv.hiInf && nv.hi != ivCur.hi)) {
                    ivCur = nv;
                    changed = true;
                }
            }
        }
        // (B2) Degree-2 contraction: c2·v² + c1·v + c0 rel 0 ⇒ complete the square
        // (c2(v+s)² + D, with s = c1/(2c2), D = c0 − c1²/(4c2)) ⇒ bound (v+s)² ⇒ bound v.
        // Generalises the sum-of-squares lever (c1=0, the hong family Σx²<1 ⇒ |x_i|<1
        // ⇒ |Πx|<1, contra Πx>1) to the FULL single-var quadratic (c1≠0, e.g. x²−2x+2<0
        // ⇒ (x−1)²<−1 ⇒ infeasible). Sound: every step uses the sound interval ops, so
        // [−r−s.hi, r−s.lo] ⊇ the true v-range — the box stays an over-approximation.
        for (size_t ci : cons) {
            const RationalPolynomial& rp = *satRp[ci];
            Relation rel = input.constraints[ci].rel;
            for (auto& [v, ivCur] : box) {
                if (rp.degree(v) != 2) continue;
                std::vector<RationalPolynomial> co = rp.coefficients(v);  // [c0, c1, c2]
                if (co.size() < 3) continue;
                Iv c2 = ivEval(co[2], m, box), c1 = ivEval(co[1], m, box), c0 = ivEval(co[0], m, box);
                if (!ivExcludesZero(c2)) continue;                       // need sign(c2) definite
                const bool c2pos = (!c2.loInf && c2.lo > 0);
                // s = c1/(2c2) (vertex shift); D = c0 − c1²/(4c2) (completed-square value).
                const Iv s = ivMul(c1, ivRecip(ivMul(Iv::point(mpq_class(2)), c2)));
                if (s.loInf || s.hiInf) continue;                        // unbounded shift ⇒ no finite box
                const Iv D = ivAdd(c0, ivNeg(ivMul(ivMul(c1, c1),
                                            ivRecip(ivMul(Iv::point(mpq_class(4)), c2)))));
                // UPPER bound on (v+s)² (⇒ a finite box for v):
                //   c2>0, rel < / ≤ 0  : (v+s)² ≤ −D/c2
                //   c2<0, rel > / ≥ 0  : (v+s)² ≤ −D/c2
                //   rel = 0            : (v+s)² = −D/c2
                Iv u2; bool haveUpper = false;
                if (rel == Relation::Lt || rel == Relation::Leq) {
                    if (c2pos) { u2 = ivMul(ivNeg(D), ivRecip(c2)); haveUpper = true; }
                } else if (rel == Relation::Gt || rel == Relation::Geq) {
                    if (!c2pos) { u2 = ivMul(ivNeg(D), ivRecip(c2)); haveUpper = true; }
                } else if (rel == Relation::Eq) {
                    u2 = ivMul(ivNeg(D), ivRecip(c2)); haveUpper = true;
                }
                if (!haveUpper || u2.hiInf) continue;                    // no finite (v+s)² upper bound
                const mpq_class U = u2.hi;
                if (U < 0) { setConf(ci); return true; }                 // (v+s)² ≤ U<0 ⇒ infeasible
                const mpq_class r = ratSqrtUpper(U);
                // v+s ∈ [−r,r] ⇒ v ∈ [−r−s.hi, r−s.lo] (sound outer bound over s's interval).
                Iv tight; tight.loInf = false; tight.lo = -r - s.hi; tight.hiInf = false; tight.hi = r - s.lo;
                Iv nv = ivIntersect(ivCur, tight);
                if (nv.empty()) { setConf(ci); return true; }
                if (nv.loInf != ivCur.loInf || nv.hiInf != ivCur.hiInf ||
                    (!nv.loInf && nv.lo != ivCur.lo) || (!nv.hiInf && nv.hi != ivCur.hi)) {
                    ivCur = nv;
                    changed = true;
                }
            }
        }
        if (!changed) break;
    }
    return false;
}

// M2 (true ICP): prove the subtree under rational prefix `m` infeasible by box
// consistency. Sound by over-approximation — see header. Returns true ⇒ no completion
// of `m` can satisfy all constraints ⇒ safe to prune (never over-prunes a real model).
bool CdcacCore::subtreeBoxInfeasible(const std::unordered_map<VarId, mpq_class>& m,
                                     const CdcacInput& input) {
    ++g_icpCalls;
    std::unordered_map<VarId, Iv> box;
    bool inf = propagateBox(satRp_, satSafe_, m, input, box);
    if (inf) ++g_icpPrunes;
    return inf;
}

// Like subtreeBoxInfeasible but carries the FULL prefix assignment: rational coords
// as exact points and ALGEBRAIC coords as their isolating interval [lower, upper].
// The algebraic interval is a sound tight box (the true value lies inside), strictly
// better than dropping the coord to (−∞,∞) — so the over-approximation box is tighter
// and the empty-box prune fires on more subtrees, while never over-pruning a real
// model. Used by the default algebraic SAT-first descent (trySatSampleFirstAlg).
bool CdcacCore::subtreeBoxInfeasiblePrefix(const SamplePoint& prefix,
                                           const CdcacInput& input) {
    std::unordered_map<VarId, mpq_class> m;
    std::unordered_map<VarId, Iv> seedBox;
    for (size_t i = 0; i < prefix.varOrder.size(); ++i) {
        const RealAlg& pv = prefix.values[i];
        if (pv.isRational()) m.emplace(prefix.varOrder[i], pv.rational);
        else if (pv.isAlgebraic()) {
            Iv iv; iv.lo = pv.root.lower; iv.hi = pv.root.upper;
            seedBox.emplace(prefix.varOrder[i], iv);
        }
    }
    if (m.empty() && seedBox.empty()) return false;
    ++g_icpCalls;
    std::unordered_map<VarId, Iv> box;
    bool inf = propagateBox(satRp_, satSafe_, m, input, box, nullptr,
                            seedBox.empty() ? nullptr : &seedBox);
    if (inf) ++g_icpPrunes;
    return inf;
}

bool CdcacCore::topLevelBoxInfeasible(const CdcacInput& input) {
    // Independent RationalPolynomial cache (do NOT disturb satRp_/satSafe_, which the
    // SAT-first owns with its own degree caps): build it, then run the HC4 box fixpoint
    // over the EMPTY assignment. An infeasible box ⇒ globally UNSAT (sound: box ⊇ feasible).
    std::vector<std::optional<RationalPolynomial>> rps(input.constraints.size());
    std::vector<bool> safe(input.constraints.size(), false);
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        auto rp = RationalPolynomial::fromPolyId(input.constraints[ci].poly, *kernel_);
        if (!rp) continue;
        long td = 0;
        for (const auto& [key, coeff] : rp->terms()) {
            (void)coeff; long md = 0;
            for (const auto& [v, e] : key) { (void)v; md += e; }
            if (md > td) td = md;
        }
        safe[ci] = (td <= 20);   // skip very-high-degree (wide intervals, slow ivEval)
        rps[ci] = std::move(rp);
    }
    std::unordered_map<VarId, mpq_class> emptyM;
    std::unordered_map<VarId, Iv> box;
    return propagateBox(rps, safe, emptyM, input, box);
}

std::optional<std::pair<size_t, Sign>> CdcacCore::intervalFpViolation(
    const SamplePoint& prefix, const CdcacInput& input) {
    // Build the assignment box: rational coords as exact points, ALGEBRAIC coords as
    // their isolating interval [lower,upper] (a sound tight box — the true value lies
    // inside). Previously this bailed on any algebraic coordinate, so deep tower levels
    // (algebraic prefixes) got NO box-consistency prune; carrying the algebraic interval
    // lets the partial-prune fire there too, only ever over-approximating (box ⊇
    // feasible) so it never over-prunes a real model.
    std::unordered_map<VarId, mpq_class> m;
    std::unordered_map<VarId, Iv> seedBox;
    for (size_t i = 0; i < prefix.values.size(); ++i) {
        const RealAlg& pv = prefix.values[i];
        if (pv.isRational()) m[prefix.varOrder[i]] = pv.rational;
        else { Iv iv; iv.lo = pv.root.lower; iv.hi = pv.root.upper; seedBox[prefix.varOrder[i]] = iv; }
    }
    // Run the full box-consistency fixpoint: it CONTRACTS the unassigned vars'
    // intervals (degree-1 HC4), under which far more constraints become strictly
    // single-signed than over the raw R^n — so this fires much more than the prior
    // unbounded single-constraint check. propagateBox surfaces a strict-signed
    // conflicting constraint when the infeasibility is of the (A) range type; an
    // (B)-type empty-box infeasibility has no single invariant sign and is skipped
    // (sound — just no prune). Sound throughout (box ⊇ feasible projection).
    std::unordered_map<VarId, Iv> box;
    std::optional<std::pair<size_t, Sign>> aConf;
    bool inf = propagateBox(satRp_, satSafe_, m, input, box, &aConf,
                            seedBox.empty() ? nullptr : &seedBox);
    if (!inf || !aConf) return std::nullopt;
    // Confirm the surfaced sign genuinely violates the relation.
    if (relationHolds(aConf->second, input.constraints[aConf->first].rel))
        return std::nullopt;
    return aConf;
}

std::optional<std::pair<size_t, Sign>> CdcacCore::boxSectorViolation(
    const SamplePoint& prefix, VarId var, const mpq_class& lo, const mpq_class& hi,
    const CdcacInput& input) {
    std::unordered_map<VarId, mpq_class> m;
    for (size_t i = 0; i < prefix.values.size(); ++i) {
        if (!prefix.values[i].isRational()) return std::nullopt;   // defensive
        m[prefix.varOrder[i]] = prefix.values[i].rational;
    }
    // Pin the current variable to its cell interval [lo,hi]; deeper vars stay R.
    Iv cellIv; cellIv.lo = lo; cellIv.hi = hi;       // finite both ends (a sector gap)
    std::unordered_map<VarId, Iv> seed{ {var, cellIv} };
    std::unordered_map<VarId, Iv> box;
    std::optional<std::pair<size_t, Sign>> aConf;
    bool inf = propagateBox(satRp_, satSafe_, m, input, box, &aConf, &seed);
    if (!inf || !aConf) return std::nullopt;
    if (relationHolds(aConf->second, input.constraints[aConf->first].rel))
        return std::nullopt;
    return aConf;
}

// M1 box HINT: re-rank/prune the root-cell candidate list using box[k]. The cells
// themselves come from root isolation (satSampleCandidates), NOT from the box — the
// box is a coarse interval over-approximation and is used here ONLY as a heuristic:
// drop candidates it proves infeasible, add one interior sector sample, and rank.
// It is never the source of feasible cells nor a completeness/UNSAT basis. Sound for
// SAT: the leaf still exact-validates; this only changes WHICH values are tried first.
static void refineCandidatesToBox(std::vector<mpq_class>& cands, const Iv& feas,
                                  long maxBits) {
    // box[k] is a HEURISTIC HINT only — NOT the source of feasible cells. The
    // root-cell candidates (satSampleCandidates: specializeToUnivariate +
    // isolateRealRoots → sections + sector midpoints) remain the value source. box[k]
    // is used to (1) DROP candidates it proves infeasible (box ⊇ feasible projection,
    // so outside-box values genuinely cannot extend to a model — sound prune the local
    // forward-check can't see) and (2) ADD one interior sector sample. We deliberately
    // do NOT add box ENDPOINTS as values (an open inequality bound is infeasible) and
    // never treat box as a cell or a completeness basis.
    auto inFeas = [&](const mpq_class& q) {
        if (!feas.loInf && q < feas.lo) return false;
        if (!feas.hiInf && q > feas.hi) return false;
        return true;
    };
    std::vector<mpq_class> out;
    for (const auto& q : cands) if (inFeas(q)) out.push_back(q);   // (1) drop box-infeasible
    // (2) one strictly-interior rational of the finite box, as a sector sample.
    if (!feas.loInf && !feas.hiInf && feas.lo < feas.hi) {
        mpq_class mid = simplestRationalIn(feas.lo, feas.hi);
        if (mid > feas.lo && mid < feas.hi && mpqBitLen(mid) <= maxBits) out.push_back(mid);
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    // Simplest-first: smallest |value|, ties by denominator then value (real models
    // cluster at small simple rationals).
    std::stable_sort(out.begin(), out.end(), [](const mpq_class& a, const mpq_class& b) {
        mpq_class aa = abs(a), bb = abs(b);
        if (aa != bb) return aa < bb;
        if (a.get_den() != b.get_den()) return a.get_den() < b.get_den();
        return a < b;
    });
    if (!out.empty()) cands.swap(out);   // keep the originals if the box emptied the list
}

CdcacResult CdcacCore::trySatSampleFirst(int k, SamplePoint& prefix,
                                         const CdcacInput& input, long& budget) {
    int n = static_cast<int>(input.varOrder.size());
    // Exact rational assignment from the prefix, keyed by VarId (SAT-first only
    // samples rationals). Fed to exactSignAt — pure mpq, never libpoly.
    auto buildMap = [&]() {
        std::unordered_map<VarId, mpq_class> m;
        for (size_t i = 0; i < prefix.varOrder.size(); ++i)
            if (prefix.values[i].isRational())
                m.emplace(prefix.varOrder[i], prefix.values[i].rational);
        return m;
    };
    if (k == n) {
        // Leaf: exact-validate EVERY constraint at the rational point via the
        // cached poly + exactSignAt (pure mpq, crash-free). All hold ⇒ sound model
        // (invariant 1). Any failure — or a constraint without a cached exact poly,
        // which cannot be confirmed crash-free — ⇒ keep searching (never UNSAT).
        auto m = buildMap();
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            if (ci >= satRp_.size() || !satRp_[ci])
                return CdcacResult::mkUnknown(CdcacUnknownReason::None);
            if (!satRelHolds(exactSignAt(*satRp_[ci], m), input.constraints[ci].rel))
                return CdcacResult::mkUnknown(CdcacUnknownReason::None);
        }
        return CdcacResult::mkSat(prefix);
    }
    if (budget <= 0) return CdcacResult::mkUnknown(CdcacUnknownReason::None);
    VarId var = input.varOrder[k];
    // Increment 3: if this lower-var prefix matches a learned dead cell for level
    // k, var k is already known infeasible here — prune the whole subtree (sound
    // for SAT: the projection cell certifies infeasibility; a too-coarse cell only
    // misses a model, never a wrong verdict).
    if (satNlsatEnabled_ && k > 0 && prefixInLearnedDeadCell(k, buildMap()))
        return CdcacResult::mkUnknown(CdcacUnknownReason::None);
    std::vector<mpq_class> cands = satSampleCandidates(var, prefix, input);
    // M1 (feasible-cell value selection): if the box-consistency fixpoint can contract
    // var k's feasible region under the current prefix, bias candidates into that cell —
    // dropping values the box proves infeasible (e.g. 0 for a strictly-positive-forced
    // var) and adding interior reps (fractions a fixed {0,±1,±2,±3} list never reaches).
    // If the prefix is already box-infeasible, the whole level is dead — prune now.
    if (satFirstLookaheadEnabled_) {
        std::unordered_map<VarId, Iv> box;
        if (propagateBox(satRp_, satSafe_, buildMap(), input, box)) {
            ++g_icpCalls; ++g_icpPrunes;
            return CdcacResult::mkUnknown(CdcacUnknownReason::None);
        }
        ++g_icpCalls;
        auto it = box.find(var);
        if (it != box.end() && !it->second.isAll())
            refineCandidatesToBox(cands, it->second, satSampleMaxBits_);
    }
    std::unordered_set<VarId> assigned;
    for (VarId v : prefix.varOrder) assigned.insert(v);
    assigned.insert(var);
    bool anyFeasible = false;   // increment 3: did ANY candidate survive forward-check?
    for (auto& q : cands) {
        if (budget <= 0) break;
        --budget;
        // Wall-clock cap: bail (exhaust budget → fall through to projection) once
        // the search exceeds satFirstMs_. Checked every 1024 nodes to keep the
        // clock-call cost negligible. Soundness-neutral (SAT only on a validated
        // leaf; expiry just means "no model found here", never a wrong verdict).
        if (satFirstMs_ > 0 && (budget & 1023) == 0) {
            auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                          std::chrono::steady_clock::now() - satFirstT0_).count();
            if (ms > satFirstMs_) { budget = 0; break; }
        }
        prefix.push(var, RealAlg::fromRational(q));
        // Forward-checking via the EXACT mpq sign (crash-free): prune the moment a
        // constraint's vars are all assigned and it is violated at this concrete
        // rational point. Sound — removes only already-inconsistent points.
        auto m = buildMap();
        bool pruned = false;
        for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
            if (ci >= satRp_.size() || !satRp_[ci]) continue;
            bool allAssigned = true, hasVar = false;
            for (VarId v : satRp_[ci]->variables()) {
                if (v == var) hasVar = true;
                if (!assigned.count(v)) { allAssigned = false; break; }
            }
            // Only constraints NEWLY fully-determined at THIS level (contain `var`).
            // Constraints full at a shallower level were already checked when their
            // last var was fixed and are independent of `var` — re-checking is pure
            // redundant work, and the k==n leaf re-validates every constraint, so no
            // soundness is lost. Mirrors solveLevel's hasVar-gated forward-prune.
            if (!hasVar || !allAssigned) continue;
            if (!satRelHolds(exactSignAt(*satRp_[ci], m), input.constraints[ci].rel)) { pruned = true; break; }
        }
        // (Learned dead cells are checked once per prefix at the TOP of the level,
        // not per-candidate — they constrain the lower vars, not var k.)
        // M2 forward infeasibility (true ICP): box-consistency propagation over the
        // UNASSIGNED vars under this extended prefix. If the over-approx range of any
        // constraint excludes its relation, or contraction empties a var's box, the
        // prefix cannot be completed — prune NOW (early/shallow conflict) instead of
        // descending and failing late. Sound: never over-prunes a real model.
        if (!pruned && satFirstLookaheadEnabled_ && subtreeBoxInfeasible(m, input))
            pruned = true;
        if (pruned) { prefix.pop(); continue; }
        anyFeasible = true;
        CdcacResult r = trySatSampleFirst(k + 1, prefix, input, budget);
        prefix.pop();
        if (r.status == CdcacStatus::Sat) return r;
    }
    // Increment 3: if no sampled value of var k survived the forward-check, the
    // feasible set for var k under this prefix is (empirically) empty — a level-k
    // conflict. Explain it LAZILY by projecting ONLY the univariate-in-k core
    // (eliminating var k) and recording each result as a feasibility cut over the
    // prefix vars, so a sibling re-search of var k-1 skips this dead region. This
    // is the z3-nlsat lever: project on demand at the conflict, never eagerly.
    if (satNlsatEnabled_ && !anyFeasible && !cands.empty() && k > 0)
        projectConflictCore(k, var, prefix, input);
    return CdcacResult::mkUnknown(CdcacUnknownReason::None);
}

// Increment 3: lazy conflict-driven projection. var k's feasible set is empty
// under `prefix`; gather the univariate-in-k constraints (the only polys that
// can have pruned here — lower-only constraints were already satisfied by the
// surviving prefix) as the conflict core, project them ELIMINATING var k, and
// record ONE dead CELL = the conjunction of the projected polys' current signs
// at the prefix. That sign-cell is where var k's root structure (hence its empty
// feasibility) is invariant, so any sibling prefix in the SAME cell is also
// infeasible for var k and is pruned (prefixInLearnedDeadCell). Pruning the
// intersection (all signs match), not each half-space's union, is what keeps it
// from excluding the SAT region (the iter-18 over-prune bug).
void CdcacCore::projectConflictCore(int k, VarId var, const SamplePoint& prefix,
                                    const CdcacInput& input) {
    if (!satExplainPolicy_)
        satExplainPolicy_ = std::make_unique<CollinsConservativePolicy>();

    std::unordered_set<VarId> assigned;
    for (VarId v : prefix.varOrder) assigned.insert(v);
    assigned.insert(var);

    // Projection-cost firewall. Collins projection is exponential in the number
    // of distinct variables and in the per-poly degree in the eliminated var
    // (resultant degree = product of input degrees). Projecting the FULL
    // univariate-in-k set on a matrix-product core blows GMP up (uncatchable
    // abort). So we bound the core to a low-dimensional, low-degree subset; if no
    // safe subset exists we skip learning entirely and the SAT search proceeds
    // EXACTLY as the committed baseline (which already finds matrix-1's model).
    // This guards the OPTIONAL learning step — it never turns a model into
    // unknown (NOT a solve budget).
    // Defaults widened (was 2/3/3) now that learned conflicts are CELLS (sign
    // conjunctions), not union half-spaces: more polys in the core → more sign
    // conditions → a MORE specific cell → prunes only the certified-infeasible
    // region (tight defaults made coarse cells that over-pruned the SAT region —
    // matrix-1 NLSAT was TO, now sat with these). Lazy projection is tractable at
    // this width (iter-18: no explosion even at 12/30/16). Still bounded so a
    // single conflict's projection stays cheap.
    static const int kMaxCoreVars =
        env::paramInt("XOLVER_NRA_NLSAT_MAX_CORE_VARS", 8) > 0
            ? env::paramInt("XOLVER_NRA_NLSAT_MAX_CORE_VARS", 8) : 8;
    static const int kMaxCorePolys =
        env::paramInt("XOLVER_NRA_NLSAT_MAX_CORE_POLYS", 20) > 0
            ? env::paramInt("XOLVER_NRA_NLSAT_MAX_CORE_POLYS", 20) : 20;
    static const int kMaxElimDeg =
        env::paramInt("XOLVER_NRA_NLSAT_MAX_ELIM_DEG", 10) > 0
            ? env::paramInt("XOLVER_NRA_NLSAT_MAX_ELIM_DEG", 10) : 10;

    // Degree of `rp` in var `var` (max monomial exponent of var).
    auto degInVar = [&](const RationalPolynomial& rp) {
        long d = 0;
        for (const auto& [key, coeff] : rp.terms()) {
            (void)coeff;
            for (const auto& [v, e] : key) if (v == var && (long)e > d) d = (long)e;
        }
        return d;
    };

    // Candidate univariate-in-k polys, tagged with elimination degree + var set.
    struct Cand { const RationalPolynomial* rp; SatLit reason; long elimDeg; std::set<VarId> vars; };
    std::vector<Cand> cands_;
    for (size_t ci = 0; ci < input.constraints.size(); ++ci) {
        if (ci >= satRp_.size() || !satRp_[ci]) continue;
        bool univ = true, hasVar = false;
        std::set<VarId> vs;
        for (VarId v : satRp_[ci]->variables()) {
            if (!assigned.count(v)) { univ = false; break; }
            if (v == var) hasVar = true; else vs.insert(v);
        }
        if (!univ || !hasVar) continue;
        if (projectedPolyIntractable(*satRp_[ci])) continue;  // never feed an explosive poly to project()
        long ed = degInVar(*satRp_[ci]);
        if (ed == 0 || ed > kMaxElimDeg) continue;   // too costly / not in var
        cands_.push_back({&*satRp_[ci], input.constraints[ci].reason, ed, std::move(vs)});
    }
    if (cands_.size() < 2) return;

    // Greedily build a minimal, low-dimensional core: cheapest elimination degree
    // first, keeping the union of LOWER (eliminated-away) vars within kMaxCoreVars.
    std::sort(cands_.begin(), cands_.end(),
              [](const Cand& a, const Cand& b) { return a.elimDeg < b.elimDeg; });
    std::vector<ReasonedPolynomial> core;
    std::set<VarId> unionVars;
    for (const auto& c : cands_) {
        if ((int)core.size() >= kMaxCorePolys) break;
        std::set<VarId> u = unionVars;
        u.insert(c.vars.begin(), c.vars.end());
        if ((int)u.size() > kMaxCoreVars) continue;   // would over-dimension the projection
        unionVars.swap(u);
        core.push_back({*c.rp, PolyRole::ConstraintPolynomial, {c.reason}});
    }
    if (core.size() < 2) return;   // need ≥2 polys for a genuine root-overlap conflict

    ProjectionContext ctx;
    ctx.level = k;
    ctx.currentVar = var;
    ctx.prefix = prefix;
    ctx.kernel = kernel_;
    ctx.algebra = algebra_;

    ProjectionInput in;
    in.polys = core;
    in.eliminateVar = var;          // eliminate var k ⇒ polys over the prefix vars
    in.baseCell = Cell();
    in.baseCell.var = var;

    PolicyProjectionResult pr;
    try {
        pr = satExplainPolicy_->project(in, ctx);
    } catch (...) {
        return;   // projection is best-effort; never let it break the SAT search
    }

    std::unordered_map<VarId, mpq_class> m;
    for (size_t i = 0; i < prefix.varOrder.size(); ++i)
        if (prefix.values[i].isRational())
            m.emplace(prefix.varOrder[i], prefix.values[i].rational);

    // Build ONE dead cell = the CONJUNCTION of the projection polys' current signs
    // at the conflict prefix. This is the McCallum/Lazard sign-invariant cell of the
    // lower vars over which var k's root structure (hence its empty feasibility) is
    // constant. Pruning the INTERSECTION of these sign conditions (all must match)
    // excludes only the certified-infeasible cell — NOT each half-space's union,
    // which over-pruned the SAT region (iter 18). A poly with sign 0 at the prefix
    // sits on a cell wall; include it as a == 0 condition (the wall is part of the
    // cell boundary). Soundness-for-SAT: a too-coarse cell only misses a model.
    std::vector<SatSignCond> conds;
    for (const auto& rp : pr.projectionPolys) {
        if (rp.poly.contains(var)) continue;   // must be eliminated (over prefix vars only)
        if (projectedPolyIntractable(rp.poly)) continue;  // skip a huge poly (slow exactSignAt)
        bool allAssigned = true;
        for (VarId v : rp.poly.variables())
            if (!m.count(v)) { allAssigned = false; break; }
        if (!allAssigned) continue;
        if (rp.poly.variables().empty()) continue;   // constant ⇒ no cell constraint
        conds.push_back({rp.poly, exactSignAt(rp.poly, m)});
    }
    // Need ≥1 non-trivial sign condition to define a cell; an empty conjunction
    // would match EVERY prefix (prune everything) — refuse it.
    if (!conds.empty())
        satDerivedCells_.push_back({k, std::move(conds)});
}

// True iff the lower-var assignment `m` matches ALL sign conditions of some learned
// dead cell tagged for this `level`. That certifies var[level] infeasible here, so
// the caller prunes the subtree. Intersection (every cond) — never union.
bool CdcacCore::prefixInLearnedDeadCell(int level,
                                        const std::unordered_map<VarId, mpq_class>& m) const {
    for (const auto& cell : satDerivedCells_) {
        if (cell.level != level || cell.conds.empty()) continue;
        bool allMatch = true;
        for (const auto& c : cell.conds) {
            // every var of the cell poly must be assigned in m (lower vars are)
            bool ok = true;
            for (VarId v : c.poly.variables())
                if (!m.count(v)) { ok = false; break; }
            if (!ok || exactSignAt(c.poly, m) != c.sign) { allMatch = false; break; }
        }
        if (allMatch) return true;   // prefix inside a certified-infeasible cell
    }
    return false;
}

Cell CdcacCore::buildLeafConflictCell(const CdcacConstraint& /*c*/, const SamplePoint& /*sample*/, VarId /*var*/) {
    // P1: implemented inline in solveLevel.
    return Cell{};
}

// FAIL-SAFE per-cell gate: every cell in a covering certificate must carry a
// COMPLETE LazardCellCertificate, and (recursively) every cell of every nested
// child covering must too. Absent cert ⇒ incomplete (fail-safe). This is the
// predicate that lets the line-905 gate trust a covering whose per-solve
// unsatTrustworthy_ was poisoned by an unrelated exploratory branch.
bool CdcacCore::coveringCellsAllComplete(const CoveringCertificate& cert) {
    if (cert.cells.empty()) return false;  // empty covering proves nothing
    for (const auto& cc : cert.cells) {
        if (!cc.lazardCert || !cc.lazardCert->isComplete()) return false;
        // Recurse into the child covering of this cell (the deeper UNSAT proof).
        if (cc.certificate.childCoverCert) {
            if (!coveringCellsAllComplete(*cc.certificate.childCoverCert)) return false;
        }
    }
    return true;
}

LazardCellCertificate CdcacCore::makeLazardCellCert(
    bool levelBoundaryComplete,
    bool levelRootIsolationComplete,
    const CdcacResult& childRes,
    std::optional<FullLineReason> fullLineReason) const {
    LazardCellCertificate lc;
    lc.closureId = lazardClosure_.closureId();
    lc.prefixCellId = 0;
    lc.fullLineReason = fullLineReason;

    // closure underpins every level's boundaries; required for the whole chain.
    lc.closureComplete = closureComplete_;
    // This cell's own delineating-boundary construction (specialization /
    // vanish-recovery) was complete.
    lc.valuationComplete = levelBoundaryComplete;
    lc.rootIsolationComplete = levelBoundaryComplete && levelRootIsolationComplete;
    lc.rootMergeComplete = levelBoundaryComplete;  // mergeRoots succeeded (else Unknown earlier)

    // prefixComplete = the recursive child UNSAT proof below this cell was
    // ITSELF fully per-cell complete. A cell with no child covering (shouldn't
    // happen for a generalized conflict cell, but fail-safe) is treated as
    // incomplete. The child covering's leaf base-case is marked complete in
    // checkFullSample.
    if (childRes.status == CdcacStatus::Unsat && childRes.coveringCert) {
        lc.prefixComplete = coveringCellsAllComplete(*childRes.coveringCert);
    } else {
        lc.prefixComplete = false;
    }
    return lc;
}

BuildCellResult CdcacCore::buildConflictCell(
    int k,
    const RealAlg& sample,
    CdcacResult& childRes,
    const CdcacInput& input,
    const RootSet& roots,
    bool levelBoundaryComplete,
    std::optional<FullLineReason> fullLineReason) {
    // P2b: shallow generalization only.
    // Uses current-level constraint roots and full child reasons.
    // Does not perform projection-driven parent generalization.
    // Guards are recorded for future certificate use only.

    if (childRes.status != CdcacStatus::Unsat || !childRes.unsat) {
        BuildCellResult bcr;
        bcr.status = BuildCellStatus::Unknown;
        bcr.unknownReason = CdcacUnknownReason::InternalInvariantViolation;
        return bcr;
    }

    VarId var = input.varOrder[k];

    auto lookup = CoveringManager::cellContaining(algebra_, var, sample, roots);
    if (lookup.status == CellLookupStatus::Unknown) {
        BuildCellResult bcr;
        bcr.status = BuildCellStatus::Unknown;
        bcr.unknownReason = CdcacUnknownReason::AlgebraicComparisonInconclusive;
        return bcr;
    }
    if (lookup.status == CellLookupStatus::InvalidInput) {
        BuildCellResult bcr;
        bcr.status = BuildCellStatus::Unknown;
        bcr.unknownReason = CdcacUnknownReason::InternalInvariantViolation;
        return bcr;
    }

    Cell cell = lookup.cell;
    cell.reasons = childRes.unsat->reasons;

    // V2-6: populate section data for Section cells
    if (cell.isSection() && sample.isAlgebraic()) {
        SectionData sd;
        sd.squarefreeDefiningPoly = sample.root.definingPoly;
        sd.origin.squarefreeDefiningPoly = sample.root.definingPoly;
        sd.origin.mainVar = var;
        sd.origin.level = k;
        sd.origin.rootIndex = sample.root.rootIndex;
        cell.section = std::move(sd);
    }

    // Guards: constraint polynomials (shallow, no projection in P2b)
    std::vector<PolyId> guards = collectPolys(input.constraints);
    cell.guards = std::move(guards);

    // V3: Build CellCertificate
    CellCertificate cert;
    cert.kind = CellCertificateKind::LiftedCoveringInvariant;
    cert.level = k;
    cert.var = var;
    cert.cell = cell;  // copy
    cert.guards = guards;

    // Convert child result reasons to CertificateReasonLit
    for (SatLit lit : childRes.unsat->reasons) {
        bool found = false;
        for (const auto& c : input.constraints) {
            if (c.reason == lit) {
                CertificateReasonLit crl;
                crl.lit = lit;
                crl.atom = NullAtom;
                crl.polarity = true;
                crl.normalized = {c.poly, c.rel};
                cert.reasons.push_back(std::move(crl));
                found = true;
                break;
            }
        }
        if (!found) {
            // Reason not found in current constraints: may be from deeper level.
            // Add minimal CertificateReasonLit.
            CertificateReasonLit crl;
            crl.lit = lit;
            crl.atom = NullAtom;
            crl.polarity = true;
            cert.reasons.push_back(std::move(crl));
        }
    }

    // FAIL-SAFE per-cell gate: build this cell's Lazard completeness certificate
    // BEFORE childRes.coveringCert is moved away (makeLazardCellCert reads it to
    // gate prefixComplete on the child covering's per-cell completeness).
    LazardCellCertificate lazardCert =
        makeLazardCellCert(levelBoundaryComplete, /*levelRootIsolationComplete=*/true,
                           childRes, fullLineReason);

    // V3: Inherit child covering certificate and atomConditions
    if (childRes.coveringCert) {
        // Copy atomConditions from all child cells
        for (const auto& cc : childRes.coveringCert->cells) {
            for (const auto& ac : cc.certificate.atomConditions) {
                cert.atomConditions.push_back(ac);
            }
        }
        // Move child covering certificate as childCoverCert
        cert.childCoverCert = std::make_unique<CoveringCertificate>(
            std::move(*childRes.coveringCert));
    }

    BuildCellResult bcr;
    bcr.status = BuildCellStatus::Success;
    bcr.conflictCell = CertifiedCell{std::move(cell), std::move(cert), std::move(lazardCert)};
    return bcr;
}

CdcacResult CdcacCore::solveUnivariate(const CdcacInput& input) {
    // Fallback: delegate to solveLevel for univariate case
    SamplePoint prefix;
    return solveLevel(0, prefix, input);
}

bool CdcacCore::relationHolds(Sign s, Relation rel) const {
    switch (rel) {
        case Relation::Eq:  return s == Sign::Zero;
        case Relation::Neq: return s != Sign::Zero;
        case Relation::Lt:  return s == Sign::Neg;
        case Relation::Leq: return s == Sign::Neg || s == Sign::Zero;
        case Relation::Gt:  return s == Sign::Pos;
        case Relation::Geq: return s == Sign::Pos || s == Sign::Zero;
    }
    return false;
}

} // namespace xolver
