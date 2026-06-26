#pragma once

#include <gmpxx.h>
#include <vector>
#include <optional>

namespace xolver {

// ---------------------------------------------------------------------------
// Gomory fractional cut derivation — pure, stateless math.
//
// Given a simplex row whose basic INTEGER variable x_i has a fractional value,
// rewritten against the current point as
//     x_i = beta_i + Σ_j chat_j * y_j ,   y_j = (x_j - bound_j) >= 0,
// where every y_j is a NON-NEGATIVE INTEGER (the nonbasic variable is integer
// and sits at an integer bound), the Gomory fractional cut is
//     Σ_j frac(chat_j) * y_j >= 1 - f0,        f0 = frac(beta_i) ∈ (0,1)
// which is violated at the current point (all y_j = 0, LHS = 0 < 1 - f0 since
// f0 < 1) yet valid for every assignment in which x_i is integer and every y_j
// is a non-negative integer.
//
// Soundness proof (verified by brute force in the unit tests, the "localized
// per-cut validity check"): with chat_j = floor(chat_j) + f_j,
//   Σ frac(chat_j) y_j = (x_i - floor(beta_i) - Σ floor(chat_j) y_j) - f0
//                      = M - f0 ,  M ∈ ℤ ;
// the LHS is >= 0, so M >= f0 > 0 hence M >= 1, giving Σ frac y_j >= 1 - f0.
//
// This requires every y_j integer. A continuous (or unknown-integrality)
// nonbasic would need the trickier mixed-integer (GMI) formula; rather than
// risk it, deriveGomoryCut returns nullopt when any term is flagged
// non-integer — sound (we simply emit no cut), at the cost of coverage.
//
// The header is free of solver state: callers gather (chat_j, isInteger_j) and
// the basic var's fractional part; substituting y_j back into original
// variables and the explanation-aware emission live in the solver.
// ---------------------------------------------------------------------------

struct GmiNonbasicTerm {
    mpq_class coeff;    // chat_j: coefficient of y_j in x_i = beta_i + Σ chat_j y_j
    bool isInteger;     // whether y_j is provably a non-negative integer
};

struct GomoryCutResult {
    // Cut: Σ gamma_j y_j >= rhs, with all gamma_j >= 0 and rhs > 0.
    std::vector<mpq_class> gamma;
    mpq_class rhs;
};

// fractionalPart(q) = q - floor(q), always in [0, 1).
mpq_class gmiFractionalPart(const mpq_class& q);

// Derive the Gomory fractional cut. `f0` must be the fractional part of the
// basic variable's value, strictly in (0, 1). Returns nullopt if no sound
// useful cut exists: any non-integer term, or all coefficients integral (the
// cut would be vacuous / signal a different conflict the caller handles).
std::optional<GomoryCutResult> deriveGomoryCut(const mpq_class& f0,
                                               const std::vector<GmiNonbasicTerm>& terms);

// ---------------------------------------------------------------------------
// Gomory Mixed-Integer (GMI) cut — the strict generalization of the pure
// fractional cut above. Same row orientation:
//     x_i = beta_i + Σ_j chat_j * y_j ,   y_j = (x_j - bound_j) >= 0 ,
// x_i constrained integer, f0 = frac(beta_i) ∈ (0,1). Mapping to the standard
// tableau form x_B = b̄ - Σ ā_j x_j gives ā_j = -chat_j. The GMI cut is
//     Σ_j psi_j * y_j >= f0 ,   psi_j >= 0 ,
// with, for f_j = frac(ā_j) = frac(-chat_j):
//     integer y_j  : psi_j = f_j                       if f_j <= f0
//                    psi_j = (f0/(1-f0)) * (1 - f_j)    if f_j  > f0
//     continuous y_j: psi_j = ā_j                       if ā_j >= 0
//                     psi_j = (f0/(1-f0)) * (-ā_j)       if ā_j  < 0
//
// Unlike the pure cut, GMI NEVER bails on a continuous (non-integer) nonbasic
// — it folds it in via the continuous branch — and is at least as tight on
// integer nonbasics. At the current point (all y_j = 0) the LHS is 0 < f0, so
// the cut is violated; validity for every integer-x_i / y_j>=0 assignment is
// the classical GMI theorem (brute-force verified in the unit tests, exactly
// like deriveGomoryCut). Returns nullopt only when the cut is vacuous (all
// psi_j == 0), i.e. it carries no information beyond the row equation.
std::optional<GomoryCutResult> deriveGmiCut(const mpq_class& f0,
                                            const std::vector<GmiNonbasicTerm>& terms);

} // namespace xolver
