#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "expr/types.h"
#include <optional>
#include <vector>

namespace xolver {

class PolynomialKernel;

// ---------------------------------------------------------------------------
// Principal subresultant coefficient (PSC) chain — the algebraic core of an
// UNCONDITIONALLY SOUND (Collins) projection operator.
//
// For polynomials p, q viewed as univariate in `v`, the j-th subresultant
// S_j(v) is a polynomial of degree <= j in v; its leading coefficient (the
// coefficient of v^j in S_j) is the j-th principal subresultant coefficient
// psc_j. psc_0 equals res_v(p, q) up to sign.
//
// Collins projection needs the WHOLE chain {psc_0, ..., psc_{min(m,n)-1}},
// not just the top resultant/discriminant — that is exactly what the existing
// McCallum-style LocalProjectionEngine was missing (it emitted only psc_0).
//
// Implementation: the definitional Sylvester-submatrix determinant (Basu-
// Pollack-Roy). Chosen for verifiability — psc_0 must equal the existing
// `resultant`, psc of (f, f') must reproduce the discriminant — at the cost of
// an exponential cofactor determinant. A size budget bounds the cost; oversize
// => budgetExceeded, which the closure maps to Incomplete => Unknown (never
// UNSAT). Switching to an O(n^3) fraction-free determinant is a performance
// follow-up; it does not affect soundness.
//
// Sign is irrelevant for projection (only real zero sets are used), so p and q
// are swapped to ensure deg_v(p) >= deg_v(q) without sign bookkeeping.
// ---------------------------------------------------------------------------

struct PscChainResult {
    // psc[j] is the j-th principal subresultant coefficient, j = 0 ..
    // min(deg_v p, deg_v q) - 1, in v-ascending order. psc[0] == res_v(p,q)
    // up to sign. Zero / constant entries are kept; callers filter.
    std::vector<RationalPolynomial> psc;
    bool budgetExceeded = false;   // a required submatrix exceeded maxMatrixDim
};

// Returns the PSC chain of p, q w.r.t. v, or budgetExceeded=true if any
// required Sylvester submatrix exceeds `maxMatrixDim`. Degenerate inputs (a
// side with degree < 1 in v) yield an empty chain.
//
// `kernel` is OPTIONAL. When it is non-null AND (the env flag
// XOLVER_NRA_LIBPOLY_PSC is ON OR `forcePsc` is set), the chain is computed via
// the libpoly `pscChain` (no matrix-dimension bound, so budgetExceeded is never
// set). When `kernel` is null OR neither the flag nor forcePsc is set, the
// definitional Sylvester-submatrix determinant below is used — byte-identical
// to the historical behaviour (the determinant path is the reference oracle and
// is never deleted).
//
// `forcePsc` lets the Lazard projection operator engage the exact libpoly PSC
// path WITHOUT requiring the global env flag (the Lazard operator always wants
// the exact PSC when a kernel is available). The Collins path passes
// forcePsc=false so it stays gated on the env flag — byte-identical.
PscChainResult principalSubresultantCoefficients(
    const RationalPolynomial& p,
    const RationalPolynomial& q,
    VarId v,
    int maxMatrixDim = 9,
    PolynomialKernel* kernel = nullptr,
    bool forcePsc = false);

// Clear the per-thread PSC chain cache. Called from CacEngine::solve() so the
// cache is scoped to a single solve(); subsequent solves see a clean state.
// Cache is keyed by (p, q, v, maxMatrixDim, forcePsc, kernel-presence, libpoly-
// flag); gated on XOLVER_NRA_CAC_SR_CACHE. Sound because PSC is a pure
// mathematical function of its inputs — same key, same result.
void clearPscChainCache();

} // namespace xolver
