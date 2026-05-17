#include "theory/arith/nra/CdcacCore.h"
#include "theory/arith/nra/LocalProjection.h"
#include <algorithm>
#include <unordered_set>
#include <iostream>

namespace nlcolver {

// ------------------------------------------------------------------
// Helpers (free functions in nlcolver namespace)
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

// Helper: create a Bound from a RealAlg (preserves exactness for algebraic roots)
static Bound boundFromRealAlg(const RealAlg& ra, bool isOpen) {
    if (ra.isRational()) return Bound::rational(ra.rational, isOpen);
    return Bound::algebraic(ra.root, isOpen);
}

// Helper: try local projection to get univariate polynomials for current level
static std::vector<RootSet> tryLocalProjection(
    const std::vector<CdcacConstraint>& constraints,
    const SamplePoint& prefix,
    VarId var,
    int level,
    PolynomialKernel* kernel,
    AlgebraBackend* algebra) {

    std::vector<RootSet> result;

    // Convert constraints to RationalPolynomial
    std::vector<ReasonedPolynomial> rpConstraints;
    for (const auto& c : constraints) {
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel);
        if (!rpOpt) continue;
        rpConstraints.push_back({*rpOpt, PolyRole::ConstraintPolynomial, {c.reason}});
    }

    if (rpConstraints.empty()) return result;

    // Find the highest variable present in any constraint (above current level)
    // For V1: we eliminate the highest-level variable that appears in constraints
    // This is a simplified approach; full CDCAC would do this iteratively.
    LocalProjectionEngine engine;

    // Try eliminating each variable that's not the current variable
    std::set<VarId> allVars;
    for (const auto& rp : rpConstraints) {
        auto vars = rp.poly.variables();
        allVars.insert(vars.begin(), vars.end());
    }

    for (VarId eliminateVar : allVars) {
        if (eliminateVar == var) continue;

        auto projResult = engine.project(rpConstraints, eliminateVar);
        if (projResult.hasDegeneracy) {
            // V1: ignore degenerate projections conservatively
            continue;
        }

        // Try to convert projected polynomials to univariate in current var
        for (const auto& rp : projResult.polys) {
            if (!rp.poly.contains(var)) continue;

            // Convert to PolyId
            PolyId polyId = rp.poly.toPolyId(*kernel);
            if (polyId == NullPoly) continue;

            // Specialize to univariate (substituting prefix values for lower vars)
            UniPolyId up = algebra->specializeToUnivariate(polyId, prefix, var);
            if (up == NullUniPolyId) continue;

            RootSet roots = algebra->isolateRealRoots(up);
            if (roots.numRoots() > 0) {
                result.push_back(std::move(roots));
            }
        }
    }

    return result;
}

// ------------------------------------------------------------------
// CdcacCore implementation
// ------------------------------------------------------------------

CdcacCore::CdcacCore(PolynomialKernel* kernel, AlgebraBackend* algebra)
    : kernel_(kernel), algebra_(algebra) {}

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

    return RootSet{std::move(merged)};
}

CdcacResult CdcacCore::solve(const CdcacInput& input) {
    std::cerr << "[CDCAC] solve: varOrder.size=" << input.varOrder.size() << std::endl;
    SamplePoint prefix;
    return solveLevel(0, prefix, input);
}

CdcacResult CdcacCore::solveLevel(int k, SamplePoint& prefix, const CdcacInput& input) {
    int n = static_cast<int>(input.varOrder.size());
    if (k == n) {
        if (n == 0) {
            std::cerr << "[CDCAC] empty varOrder, checkFullSample" << std::endl;
        }
        return checkFullSample(prefix, input);
    }

    VarId var = input.varOrder[k];
    std::cerr << "[CDCAC] solveLevel k=" << k << " var=" << kernel_->varName(var) << std::endl;

    // 1. Collect polynomials that become univariate in 'var' after prefix substitution
    std::vector<PolyId> polys = collectPolys(input.constraints);
    std::vector<UniPolyId> uniPolys;
    std::vector<RootSet> rootSets;
    bool hasAlgebraicPrefix = false;
    for (const auto& v : prefix.values) {
        if (v.isAlgebraic()) {
            hasAlgebraicPrefix = true;
            break;
        }
    }

    for (PolyId p : polys) {
        if (kernel_->isConstant(p)) continue;
        UniPolyId up = algebra_->specializeToUnivariate(p, prefix, var);
        if (up == NullUniPolyId) {
            // If specialization failed due to algebraic prefix, try algebraic root isolation
            if (hasAlgebraicPrefix) {
                std::cerr << "[CDCAC]   trying algebraic isolation for poly=" << kernel_->toString(p) << std::endl;
                RootSet roots = algebra_->isolateRealRootsAlgebraic(p, prefix, var);
                std::cerr << "[CDCAC]   algebraic roots=" << roots.numRoots() << std::endl;
                if (roots.numRoots() > 0) {
                    rootSets.push_back(std::move(roots));
                }
            }
            continue;
        }
        std::cerr << "[CDCAC]   specialize poly=" << kernel_->toString(p) << std::endl;
        RootSet roots = algebra_->isolateRealRoots(up);
        std::cerr << "[CDCAC]   roots=" << roots.numRoots() << std::endl;
        if (!algebra_->validateRootIsolation(up, roots)) {
            std::cerr << "[CDCAC]   validate failed" << std::endl;
            return CdcacResult::mkUnknown(CdcacUnknownReason::RootIsolationInvalid);
        }
        // P2c: fill provenance metadata for algebraic roots
        for (auto& r : roots.roots) {
            if (r.isAlgebraic()) {
                r.root.origins.push_back({p, var, k});
            }
        }
        uniPolys.push_back(up);
        rootSets.push_back(std::move(roots));
    }

    // 1b. If no local univariate polynomials, try local projection
    if (uniPolys.empty() && rootSets.empty() && k + 1 < n) {
        std::cerr << "[CDCAC]   no local polys, trying projection" << std::endl;
        auto projRoots = tryLocalProjection(input.constraints, prefix, var, k, kernel_, algebra_);
        for (auto& rs : projRoots) {
            std::cerr << "[CDCAC]   projection roots=" << rs.numRoots() << std::endl;
            rootSets.push_back(std::move(rs));
        }
    }

    // 2. Merge all roots
    auto mergedOpt = mergeRoots(rootSets);
    if (!mergedOpt) {
        std::cerr << "[CDCAC] mergeRoots failed (Unknown comparison)" << std::endl;
        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
    }
    RootSet allRoots = std::move(*mergedOpt);
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

    // Helper to add conflict cell
    auto addCell = [&](CellKind kind, const Bound& lower, const Bound& upper,
                       const std::vector<SatLit>& reasons, PolyId guardPoly) {
        Cell cell;
        cell.var = var;
        cell.kind = kind;
        cell.lower = lower;
        cell.upper = upper;
        cell.reasons = reasons;
        if (guardPoly != NullPoly) {
            cell.guards.push_back(guardPoly);
        }
        return cell;
    };

    std::vector<Cell> conflictCells;

    // 4. Generate and test cells
    if (allRoots.roots.empty()) {
        if (uniPolys.empty()) {
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

        // Has uniPolys but no roots: entire line is one cell
        RealAlg sample = RealAlg::fromRational(mpq_class(0));
        CdcacResult res = testAndRecurse(sample);
        std::cerr << "[CDCAC]   full-line sample result=" << (int)res.status << std::endl;
        if (res.status == CdcacStatus::Sat) return res;
        if (res.status == CdcacStatus::Unknown) return res;
        auto bcr = buildConflictCell(k, sample, res, input, allRoots);
        if (bcr.status == BuildCellStatus::Unknown) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
        }
        conflictCells.push_back(std::move(bcr.cell));
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
                    std::cerr << "[CDCAC]   sector(" << sectorLo.get_d() << "," << sectorHi.get_d() << ") result=" << (int)res.status << std::endl;
                    if (res.status == CdcacStatus::Sat) return res;
                    if (res.status == CdcacStatus::Unknown) return res;
                    auto bcr = buildConflictCell(k, sample, res, input, allRoots);
                    if (bcr.status == BuildCellStatus::Unknown) {
                        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                    }
                    conflictCells.push_back(std::move(bcr.cell));
                }
            } else {
                // First sector: (-inf, r0)
                mpq_class sectorHi = rootVal;
                mpq_class sampleQ = sectorHi - 1;
                RealAlg sample = RealAlg::fromRational(sampleQ);
                CdcacResult res = testAndRecurse(sample);
                std::cerr << "[CDCAC]   sector(-inf," << sectorHi.get_d() << ") result=" << (int)res.status << std::endl;
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                auto bcr = buildConflictCell(k, sample, res, input, allRoots);
                if (bcr.status == BuildCellStatus::Unknown) {
                    return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                }
                conflictCells.push_back(std::move(bcr.cell));
            }

            // Section at this root
            {
                CdcacResult res = testAndRecurse(root);
                std::cerr << "[CDCAC]   section[" << rootVal.get_d() << "] result=" << (int)res.status << std::endl;
                if (res.status == CdcacStatus::Sat) return res;
                if (res.status == CdcacStatus::Unknown) return res;
                auto bcr = buildConflictCell(k, root, res, input, allRoots);
                if (bcr.status == BuildCellStatus::Unknown) {
                    return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
                }
                conflictCells.push_back(std::move(bcr.cell));
            }

            prevRoot = root;
        }

        // Final sector (lastRoot, +inf)
        if (prevRoot) {
            mpq_class sectorLo = prevRoot->isRational() ? prevRoot->rational : prevRoot->root.upper;
            mpq_class sampleQ = sectorLo + 1;
            RealAlg sample = RealAlg::fromRational(sampleQ);
            CdcacResult res = testAndRecurse(sample);
            std::cerr << "[CDCAC]   sector(" << sectorLo.get_d() << ",+inf) result=" << (int)res.status << std::endl;
            if (res.status == CdcacStatus::Sat) return res;
            if (res.status == CdcacStatus::Unknown) return res;
            auto bcr = buildConflictCell(k, sample, res, input, allRoots);
            if (bcr.status == BuildCellStatus::Unknown) {
                return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
            }
            conflictCells.push_back(std::move(bcr.cell));
        }
    }

    // 5. Build covering and check
    Covering cover;
    cover.var = var;
    cover.cells = std::move(conflictCells);

    std::cerr << "[CDCAC] final cells=" << cover.cells.size() << std::endl;
    CoverageResult cov = CoveringManager::coversAllLine(algebra_, cover);
    if (cov == CoverageResult::DoesNotCover) {
        std::cerr << "[CDCAC] coversAllLine: does not cover" << std::endl;
        return CdcacResult::mkUnknown(CdcacUnknownReason::InternalInvariantViolation);
    }
    if (cov == CoverageResult::Unknown) {
        std::cerr << "[CDCAC] coversAllLine: unknown (comparison inconclusive)" << std::endl;
        return CdcacResult::mkUnknown(CdcacUnknownReason::AlgebraicComparisonInconclusive);
    }

    auto reasons = ReasonManager::minimize(cover);
    return CdcacResult::mkUnsat(std::move(cover), std::move(reasons));
}

CdcacResult CdcacCore::checkFullSample(const SamplePoint& sample, const CdcacInput& input) {
    std::vector<SatLit> conflictLits;
    for (const auto& c : input.constraints) {
        Sign sign = algebra_->signAt(c.poly, sample);
        if (sign == Sign::Unknown) {
            return CdcacResult::mkUnknown(CdcacUnknownReason::SignEvaluationInconclusive);
        }
        if (!relationHolds(sign, c.rel)) {
            conflictLits.push_back(c.reason);
        }
    }
    if (!conflictLits.empty()) {
        Covering cover;
        cover.var = input.varOrder.empty() ? NullVar : input.varOrder[0];
        Cell cell;
        cell.var = cover.var;
        cell.kind = CellKind::FullLine;
        cell.lower = Bound::negInf();
        cell.upper = Bound::posInf();
        cell.reasons = std::move(conflictLits);
        cover.cells.push_back(std::move(cell));
        auto reasons = ReasonManager::minimize(cover);
        return CdcacResult::mkUnsat(std::move(cover), std::move(reasons));
    }
    return CdcacResult::mkSat(sample);
}

Cell CdcacCore::buildLeafConflictCell(const CdcacConstraint& /*c*/, const SamplePoint& /*sample*/, VarId /*var*/) {
    // P1: implemented inline in solveLevel.
    return Cell{};
}

BuildCellResult CdcacCore::buildConflictCell(
    int k,
    const RealAlg& sample,
    const CdcacResult& childRes,
    const CdcacInput& input,
    const RootSet& roots) {
    // P2b: shallow generalization only.
    // Uses current-level constraint roots and full child reasons.
    // Does not perform projection-driven parent generalization.
    // Guards are recorded for future certificate use only.

    if (childRes.status != CdcacStatus::Unsat || !childRes.unsat) {
        return {BuildCellStatus::Unknown, Cell{}};
    }

    VarId var = input.varOrder[k];

    auto lookup = CoveringManager::cellContaining(algebra_, var, sample, roots);
    if (lookup.status == CellLookupStatus::Unknown) {
        return {BuildCellStatus::Unknown, Cell{}};
    }
    if (lookup.status == CellLookupStatus::InvalidInput) {
        return {BuildCellStatus::Unknown, Cell{}};
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

    return {BuildCellStatus::Success, std::move(cell)};
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

} // namespace nlcolver
