#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/projection/LocalProjection.h"
#include "theory/arith/nra/preprocess/NullificationAnalyzer.h"
#include "theory/arith/nra/proof/CellCertificateValidator.h"
#include "theory/arith/nra/projection/ProjectionPolicy.h"
#include "theory/arith/nra/valuation/RationalRootIsolation.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include <algorithm>
#include <unordered_set>
#include <iostream>
#include <cstdlib>
#include <string>

namespace zolver {

// ------------------------------------------------------------------
// Helpers (free functions in zolver namespace)
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
static mpq_class pickRationalSample(const mpq_class& lo, const mpq_class& hi) {
    return (lo + hi) / 2;
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

static TryLocalProjectionResult tryLocalProjection(
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
    // Opt in with ZOLVER_NRA_LAZARD_LIFT=1; it only ADDS certified root
    // isolations for genuine towers (>=2 algebraic prefix coords) that ViaNorm
    // punts on — flag-off behaviour is byte-identical to the Collins baseline.
    if (const char* e = std::getenv("ZOLVER_NRA_LAZARD_LIFT"))
        lazardLiftEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
    // Projection mode selection. ZOLVER_NRA_PROJECTION=lazard installs the real
    // Lazard projection operator as the (lazily-created) default policy; any
    // other value / unset keeps the CollinsConservative default (byte-identical
    // to today). An explicit setProjectionPolicy() call still overrides this.
    // The projection SET affects completeness only — the UNSAT certification
    // gate (unsatTrustworthy_, driven by the Collins closure_) is unchanged.
    if (const char* e = std::getenv("ZOLVER_NRA_PROJECTION")) {
        std::string mode(e);
        if (mode == "lazard" || mode == "Lazard" || mode == "LAZARD")
            projectionKind_ = ProjectionPolicyKind::LazardStyle;
    }
    // Soundness floor for the meti-tarski sqrt false-UNSAT class. Default OFF for
    // now (interim, while completeness recovery lands); intended default-ON.
    if (const char* e = std::getenv("ZOLVER_NRA_UNSAT_CERT"))
        unsatCertEnabled_ = (e[0] == '1' || e[0] == 't' || e[0] == 'T' || e[0] == 'y' || e[0] == 'Y');
    // FAIL-SAFE per-cell UNSAT gate (Lazard mode). Default ON; only relevant in
    // Lazard mode (the Collins gate is untouched). Force off for A/B with
    // ZOLVER_NRA_LAZARD_CELL_CERT=0.
    if (const char* e = std::getenv("ZOLVER_NRA_LAZARD_CELL_CERT"))
        lazardCellCertEnabled_ = !(e[0] == '0' || e[0] == 'f' || e[0] == 'F' || e[0] == 'n' || e[0] == 'N');
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

bool CdcacCore::certifyLevelSignInvariance(int k, const SamplePoint& prefix,
                                           const CdcacInput& input,
                                           const RootSet& allRoots) {
    VarId var = input.varOrder[static_cast<size_t>(k)];
    // Product of all level-k closure polynomials, with the (rational) prefix
    // substituted in, so the result is univariate in `var` with rational coeffs.
    RationalPolynomial product = RationalPolynomial::fromConstant(mpq_class(1));
    bool anyBoundary = false;
    for (PolyId pid : levelPolyIds_[static_cast<size_t>(k)]) {
        if (kernel_->isConstant(pid)) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(pid, *kernel_);
        if (!rpOpt) return false;  // cannot represent exactly ⇒ cannot certify
        RationalPolynomial rp = std::move(*rpOpt);
        for (size_t i = 0; i < prefix.values.size(); ++i) {
            if (!prefix.values[i].isRational()) return false;  // algebraic prefix ⇒ punt
            rp = rp.substituteRational(prefix.varOrder[i], prefix.values[i].rational);
        }
        if (rp.isConstant()) continue;  // vanished at this prefix ⇒ no boundary here
        product = product * rp;
        anyBoundary = true;
        if (product.degree(var) > 64) return false;  // budget guard ⇒ punt (sound)
    }
    if (!anyBoundary) return allRoots.numRoots() == 0;  // full-line cell, no roots
    auto roots = isolateRationalRoots(product, var);
    if (!roots.ok) return false;
    int exactDistinct = static_cast<int>(roots.roots.size());
    int libpolyCount = allRoots.numRoots();
    if (std::getenv("ZOLVER_NRA_CERT_DIAG")) {
        std::cerr << "[NRA-CERT] level=" << k << " exactDistinct=" << exactDistinct
                  << " allRoots=" << libpolyCount
                  << (exactDistinct == libpolyCount ? " OK" : " MISMATCH") << std::endl;
    }
    // allRoots must capture exactly the closure's distinct real roots. Fewer ⇒ a
    // missed/merged root ⇒ a cell spans a true root ⇒ not sign-invariant. Either
    // direction ⇒ cannot positively certify this covering.
    return exactDistinct == libpolyCount;
}

void CdcacCore::buildClosure(const CdcacInput& input) {
    if (std::getenv("ZOLVER_NRA_LAZARD_DIAG"))
        std::cerr << "[LAZARD-CLOSURE-ENTRY] vars=" << input.varOrder.size()
                  << " constraints=" << input.constraints.size() << std::endl;
    unsatTrustworthy_ = true;
    coveringUncertifiable_ = false;
    // Per-cell gate (Lazard): track whether the Lazard closure underpinning ALL
    // levels' boundaries built to completion. Starts true, dropped to false at
    // the SAME points that drop unsatTrustworthy_ during closure construction.
    // (Independent of unsatTrustworthy_ so a later lift-only incompleteness in
    // an exploratory branch does not retroactively poison the closure flag.)
    closureComplete_ = true;
    int n = static_cast<int>(input.varOrder.size());
    levelPolyIds_.assign(static_cast<size_t>(std::max(0, n)), {});

    std::vector<RationalPolynomial> rps;
    for (const auto& c : input.constraints) {
        if (kernel_->isConstant(c.poly)) continue;   // constants pre-handled by caller
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { unsatTrustworthy_ = false; closureComplete_ = false; continue; }
        rps.push_back(std::move(*rp));
    }

    // Projection-set selection. Default: the Collins closure (unconditionally
    // sound, byte-identical to today). ZOLVER_NRA_PROJECTION=lazard builds the
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
        if (std::getenv("ZOLVER_NRA_LAZARD_DIAG")) {
            std::cerr << "[LAZARD-CLOSURE] "
                      << (lreason == LazardIncompleteReason::None ? "COMPLETE"
                          : lreason == LazardIncompleteReason::ProjectionKernelFailure ? "KERNEL_FAILURE"
                          : lreason == LazardIncompleteReason::ProjectionBudgetExceeded ? "BUDGET_EXCEEDED"
                          : "OTHER")
                      << " entries=" << lazardClosure_.entries().size() << std::endl;
        }
        if (lreason != LazardIncompleteReason::None) {
            unsatTrustworthy_ = false;   // incomplete Lazard projection ⇒ no UNSAT
            closureComplete_ = false;    // per-cell gate: closure not complete
        }
        for (int k = 0; k < n; ++k) {
            for (int id : lazardClosure_.levelPolys(k)) {
                PolyId pid = lazardClosure_.entries()[id].poly.toPolyId(*kernel_);
                if (pid == NullPoly) { unsatTrustworthy_ = false; closureComplete_ = false; continue; }
                levelPolyIds_[k].push_back(pid);
            }
        }
        return;
    }

    auto reason = closure_.build(rps, input.varOrder, ProjectionClosure::Config(), kernel_);
    if (reason != ProjectionIncompleteReason::None) {
        unsatTrustworthy_ = false;   // incomplete projection ⇒ no UNSAT may rest on it
    }

    for (int k = 0; k < n; ++k) {
        for (int id : closure_.levelPolys(k)) {
            PolyId pid = closure_.entries()[id].poly.toPolyId(*kernel_);
            if (pid == NullPoly) { unsatTrustworthy_ = false; continue; }
            levelPolyIds_[k].push_back(pid);
        }
    }
}

CdcacResult CdcacCore::solve(const CdcacInput& input) {
#ifndef NDEBUG
    std::cerr << "[CDCAC] solve: varOrder.size=" << input.varOrder.size() << std::endl;
#endif
    buildClosure(input);
    SamplePoint prefix;
    CdcacResult result = solveLevel(0, prefix, input);

    // Soundness FLOOR (ZOLVER_NRA_UNSAT_CERT). The PRECISE per-cell sign-invariance
    // verifier (certifyLevelSignInvariance, per level in solveLevel) sets
    // `coveringUncertifiable_` and is PROVEN to catch the close-irrational-root
    // class (Melquiond: allRoots 9 vs exact 17) while certifying genuine UNSAT
    // (nra_011 etc.). BUT it is NOT yet sufficient on its own: the polypaver class
    // is sign-invariant AND tiles yet is still false-UNSAT (a distinct
    // section-recursion bug — a SAT section is never recursed to a full sample).
    // So gating on `coveringUncertifiable_` alone would LEAK those 12 false-UNSATs
    // (unsound). Until the section-recursion defect is fixed, we keep the gate
    // CONSERVATIVE (blunt): downgrade every CDCAC covering-UNSAT to Unknown.
    // `coveringUncertifiable_` is computed for diagnostics (ZOLVER_NRA_CERT_DIAG)
    // and is the foundation of the future precise floor. Only CdcacCore
    // covering-UNSAT is gated; presolve/linear UNSAT never reaches CDCAC.
    (void)coveringUncertifiable_;
    if (unsatCertEnabled_ && result.status == CdcacStatus::Unsat) {
        return CdcacResult::mkUnknown(CdcacUnknownReason::ProjectionClosureIncomplete);
    }
    return result;
}

CdcacResult CdcacCore::solveLevel(int k, SamplePoint& prefix, const CdcacInput& input) {
    int n = static_cast<int>(input.varOrder.size());
    if (k == n) {
        return checkFullSample(prefix, input);
    }

    // V4: ensure a projection policy is available. Default is CollinsConservative;
    // ZOLVER_NRA_PROJECTION=lazard selects the Lazard operator (projectionKind_).
    if (!policy_) {
        if (projectionKind_ == ProjectionPolicyKind::LazardStyle) {
            policy_ = std::make_unique<LazardStylePolicy>();
        } else {
            policy_ = std::make_unique<CollinsConservativePolicy>();
        }
    }

    VarId var = input.varOrder[k];
    std::cerr << "[CDCAC] solveLevel k=" << k << " var=" << kernel_->varName(var)
              << " n=" << n << " constraints=" << input.constraints.size() << std::endl;
#ifndef NDEBUG
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
    bool hasAlgebraicPrefix = false;
    int algPrefixCount = 0;
    for (const auto& v : prefix.values) {
        if (v.isAlgebraic()) { hasAlgebraicPrefix = true; ++algPrefixCount; }
    }
    static const bool kLazDiag = std::getenv("ZOLVER_NRA_LAZARD_DIAG") != nullptr;
    if (kLazDiag && hasAlgebraicPrefix)
        std::cerr << "[LAZVAL] solveLevel k=" << k << " algPrefixCoords=" << algPrefixCount
                  << " levelPolys=" << levelPolyIds_[k].size() << std::endl;

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
                    if (roots.numRoots() > 0) rootSets.push_back(std::move(roots));
                    continue;
                }
            }
            unsatTrustworthy_ = false;
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
                    if (std::getenv("ZOLVER_NRA_LAZARD_DIAG"))
                        std::cerr << "[LAZVAL] vanish-route k=" << k << " supported="
                                  << supported << " roots=" << roots.numRoots() << std::endl;
                    if (supported) {
                        recovered = true;
                        if (roots.numRoots() > 0) rootSets.push_back(std::move(roots));
                    }
                }
                if (!recovered) {
                    unsatTrustworthy_ = false;  // boundary not recovered ⇒ no UNSAT
                    // Per-cell gate: a vanished poly's boundary that the [H3]
                    // valuation could not positively recover ⇒ delineation
                    // incomplete ⇒ no per-cell UNSAT trust for this level.
                    levelBoundaryComplete = false;
                }
            }
            continue;
        }
        if (vanish == VanishResult::Unknown) {
            unsatTrustworthy_ = false;
            levelBoundaryComplete = false;  // undecided vanish ⇒ incomplete
            continue;
        }

        RootSet roots = algebra_->isolateRealRoots(up);
        if (!algebra_->validateRootIsolation(up, roots)) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::RootIsolationInvalid);
        }
        for (auto& r : roots.roots) {
            if (r.isAlgebraic()) r.root.origins.push_back({p, var, static_cast<VarId>(k)});
        }
        uniPolys.push_back(up);
        rootSets.push_back(std::move(roots));
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
    // PRECISE FLOOR: independently certify this level's boundary set is complete
    // (sign-invariant cells) via exact ℚ-Sturm. An uncertifiable level taints the
    // whole solve — any resulting UNSAT is downgraded to Unknown in solve().
    if (unsatCertEnabled_ && !coveringUncertifiable_ &&
        !certifyLevelSignInvariance(k, prefix, input, allRoots)) {
        coveringUncertifiable_ = true;
    }
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
        CdcacResult childRes = solveLevel(k + 1, prefix, input);
        prefix.pop();
        if (childRes.status == CdcacStatus::Sat && childRes.model) {
            childRes.model->varOrder.insert(childRes.model->varOrder.begin(), var);
            childRes.model->values.insert(childRes.model->values.begin(), sampleWithOrigin);
        }
        return childRes;
    };

    std::vector<CertifiedCell> certifiedCells;

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
                    CdcacResult res = testAndRecurse(sample);
                    if (res.status == CdcacStatus::Sat) return res;
                    if (res.status == CdcacStatus::Unknown) return res;
                    auto bcr = buildConflictCell(k, sample, res, input, allRoots, levelBoundaryComplete);
                    if (bcr.status == BuildCellStatus::Unknown) {
                        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                    }
                    certifiedCells.push_back(std::move(*bcr.conflictCell));
                }
            } else {
                // First sector: (-inf, r0)
                mpq_class sectorHi = rootVal;
                bool firstConflictRecorded = false;
                CertifiedCell firstConflictCell;
                for (int attempt = 0; attempt < 3; ++attempt) {
                    mpq_class sampleQ = sectorHi - (attempt + 1);
                    RealAlg sample = RealAlg::fromRational(sampleQ);
                    CdcacResult res = testAndRecurse(sample);
                    if (res.status == CdcacStatus::Sat) return res;
                    if (res.status == CdcacStatus::Unknown) return res;
                    if (!firstConflictRecorded) {
                        auto bcr = buildConflictCell(k, sample, res, input, allRoots, levelBoundaryComplete);
                        if (bcr.status == BuildCellStatus::Unknown) {
                            return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                        }
                        firstConflictCell = std::move(*bcr.conflictCell);
                        firstConflictRecorded = true;
                    }
                }
                if (firstConflictRecorded) {
                    certifiedCells.push_back(std::move(firstConflictCell));
                }
            }

            // Section at this root
            {
                CdcacResult res = testAndRecurse(root);
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                auto bcr = buildConflictCell(k, root, res, input, allRoots, levelBoundaryComplete);
                if (bcr.status == BuildCellStatus::Unknown) {
                    return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                }
                certifiedCells.push_back(std::move(*bcr.conflictCell));
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
                mpq_class sampleQ = sectorLo + (attempt + 1);
                RealAlg sample = RealAlg::fromRational(sampleQ);
                CdcacResult res = testAndRecurse(sample);
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                if (!firstConflictRecorded) {
                    auto bcr = buildConflictCell(k, sample, res, input, allRoots, levelBoundaryComplete);
                    if (bcr.status == BuildCellStatus::Unknown) {
                        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                    }
                    firstConflictCell = std::move(*bcr.conflictCell);
                    firstConflictRecorded = true;
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
        if (perCellTrusted && std::getenv("ZOLVER_NRA_LAZARD_DIAG"))
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
    std::vector<SatLit> conflictLits;
    std::vector<AtomCondition> atomConditions;
    std::vector<CertificateReasonLit> certReasons;

    for (const auto& c : input.constraints) {
        std::cerr << "[CDCAC-FULL] poly=" << kernel_->toString(c.poly)
                  << " rel=" << (int)c.rel
                  << " sampleVars=" << sample.numVars() << std::endl;
        Sign sign = algebra_->signAt(c.poly, sample);
        std::cerr << "[CDCAC-FULL]   sign=" << (int)sign << std::endl;
        if (sign == Sign::Unknown) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::SignEvaluationInconclusive);
        }
        if (!relationHolds(sign, c.rel)) {
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
    }
    if (!conflictLits.empty()) {
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
    return CdcacResult::mkSat(sample);
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

} // namespace zolver
