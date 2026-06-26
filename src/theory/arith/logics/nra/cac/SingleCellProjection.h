#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/cac/Covering.h"
#include "theory/arith/logics/nra/core/CdcacValue.h"   // SamplePoint, RealAlg
#include "expr/types.h"

#include <vector>

namespace xolver {

class PolynomialKernel;
class LibpolyBackend;

// ============================================================================
// CAC single-cell projection (lever 3, module B — see ../CAC.md).
//
// `characterize` is the projection step the conflict-driven covering performs
// in place of a full Collins closure: given the polynomials relevant to the
// current cell (all with main variable `elimVar`) it emits, via the COMPLETE
// Lazard operator (`lazardProjectStep`), the polynomials needed one level down.
// The result is partitioned by whether each output still contains `elimVar`:
//
//   * boundaryPolys — still contain elimVar; their real roots (isolated at the
//     sample prefix) delineate elimVar's axis at THIS level.
//   * downwardPolys — do NOT contain elimVar (leading/trailing coefficients,
//     discriminants, pairwise resultants, contents); they are the cell
//     polynomials for the NEXT level down.
//
// SOUNDNESS: `complete == false` (the Lazard operator hit an exact-gcd/budget
// limit) ⇒ the caller MUST NOT rest UNSAT on this characterization (⇒ Unknown).
// The Lazard operator is unconditionally sound when complete (no
// well-orientedness precondition), so no false-UNSAT can arise from a complete
// characterization.
//
// Pure given a kernel (the libpoly-backed exact gcd/psc path for high degree);
// `kernel == nullptr` uses the hand-rolled path (low-degree, for tests).
// ============================================================================

struct CharacterizationResult {
    bool complete = true;
    std::vector<RationalPolynomial> boundaryPolys;   // contain elimVar (this level)
    std::vector<RationalPolynomial> downwardPolys;    // free of elimVar (next level)
};

// `sample` (optional): the prefix assignment. When given, the McCallum REQUIRED
// COEFFICIENTS are added to the downward characterization — f's var-coefficients
// top-down, stopping at the first that is constant or provably nonzero at the
// sample (cvc5 requiredCoefficientsOriginal). This completes the projection for
// nullification (the degree-drop loci are delineated at lower levels) — the fix
// for the LC/TC-only set that produced false-UNSAT. Adding them is sound (a
// superset only refines cells). nullptr ⇒ all non-constant coefficients are
// added (conservative, sound).
CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel = nullptr,
                                    const SamplePoint* sample = nullptr);

// ----------------------------------------------------------------------------
// interval_from_characterization (module B.2): given THIS level's boundary
// polynomials (each with main variable `var`, from characterize), isolate their
// real roots at the sample `prefix` and return the maximal sign-invariant cell
// on var's axis that contains `sampleValue` — the interval to exclude from the
// covering. The roots' bracketing the sample become the cell's open endpoints
// (±∞ when the sample is below/above all roots); a sample equal to a root yields
// a point cell.
//
// SOUNDNESS: `supported == false` on ANY incomplete/inconclusive backend step
// (poly not representable, a curtain/vanishing boundary, a failed
// specialization with no Norm/Tower recovery, an invalid root isolation, or an
// inconclusive algebraic comparison). The caller MUST then conclude Unknown —
// never UNSAT. A `supported == true` cell is exactly delineated (every boundary
// poly's roots isolated + ordered), so it is genuinely sign-invariant.
//
// Requires libpoly (#ifdef XOLVER_HAS_LIBPOLY); the stub returns unsupported.
// ----------------------------------------------------------------------------
struct CellResult {
    bool supported = false;   // false ⇒ caller concludes Unknown
    CacInterval interval;
};

// This is the NON-LEAF lifting/boundary path. On nullification (a boundary poly
// ≡0 in `var` at the prefix) it recovers the Lazard valuation residual and
// isolates ITS roots as the genuine lifting boundary — residual→boundary is
// allowed HERE and nowhere else (the residual is a LIFTING boundary, never an
// atom's truth). It NEVER silently skips a vanishing poly. Leaf ATOMS go through
// `characterizeLeafAtom` instead, which splits truth from boundary.
CellResult intervalFromCharacterization(
    LibpolyBackend* algebra, PolynomialKernel* kernel,
    const std::vector<RationalPolynomial>& boundaryPolys,
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue);

// ----------------------------------------------------------------------------
// Leaf-atom characterization (module B.3): SPLITS the truth path from the
// boundary path for a leaf constraint `poly rel 0` on the `var` axis at `prefix`
// (the vague `skipVanishing` flag conflated these two concerns):
//
//   * poly ≡ 0 in `var` on the fiber (nullifies) ⇒ its truth is UNIFORM, decided
//     by (0 rel 0): UniformTrue or UniformFalse. NO var-boundary is produced (the
//     valuation residual is a LIFTING boundary, never a leaf atom's truth, so it
//     is NOT injected here). UniformFalse means the WHOLE fiber is infeasible —
//     the caller excludes the entire axis / raises a conflict; it is NEVER a
//     satisfied whole axis.
//   * else poly|prefix is a nonzero univariate ⇒ NonUniform: its real roots
//     delineate the maximal sign-invariant cell around `sampleValue` (the
//     boundary path; same exact-isolation contract as intervalFromCharacterization).
//
// `holdsAtSample` is the exact truth of the atom AT the sample (so the caller can
// detect SAT / which constraints are violated without a second signAt).
// `supported == false` on ANY inconclusive backend step ⇒ caller Unknown (never
// UNSAT) — same fail-closed contract as above.
// ----------------------------------------------------------------------------
enum class LeafTruth : uint8_t { UniformTrue, UniformFalse, NonUniform };

struct LeafCellResult {
    bool supported = false;
    LeafTruth truth = LeafTruth::NonUniform;
    bool holdsAtSample = false;       // exact truth of `poly rel 0` at the sample
    CacInterval interval;             // sign-invariant cell (NonUniform); all() for Uniform*
};

LeafCellResult characterizeLeafAtom(
    LibpolyBackend* algebra, PolynomialKernel* kernel,
    const RationalPolynomial& poly, Relation rel,
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue);

} // namespace xolver
