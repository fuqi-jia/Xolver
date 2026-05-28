#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/cac/Covering.h"
#include "theory/arith/nra/core/CdcacValue.h"   // SamplePoint, RealAlg
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

CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel = nullptr);

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

CellResult intervalFromCharacterization(
    LibpolyBackend* algebra, PolynomialKernel* kernel,
    const std::vector<RationalPolynomial>& boundaryPolys,
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue);

} // namespace xolver
