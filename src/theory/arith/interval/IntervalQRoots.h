#pragma once

#include <gmpxx.h>

namespace xolver {

// Sound rational sqrt with outward rounding. Both functions are total over the
// nonneg rationals (return 0 for negative input as a defensive no-op; callers
// should only invoke them on Δ ≥ 0).
//
// Precision: scaleBits bits of mantissa — default 32 gives ~10⁻¹⁰ tightness,
// which is far more than enough for interval narrowing. Higher precision is
// proportionally more expensive (mpz_sqrt on a larger integer) but never
// affects soundness — both bounds are mathematically rounded outward.
//
// Soundness contract:
//   mpqSqrtFloor(p) ≤ √p     (largest q so q² ≤ p, within precision)
//   mpqSqrtCeil(p)  ≥ √p     (smallest q so q² ≥ p, within precision)

mpq_class mpqSqrtFloor(const mpq_class& p, unsigned scaleBits = 32);
mpq_class mpqSqrtCeil(const mpq_class& p, unsigned scaleBits = 32);

} // namespace xolver
