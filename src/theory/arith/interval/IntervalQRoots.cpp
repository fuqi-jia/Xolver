#include "theory/arith/interval/IntervalQRoots.h"

namespace xolver {

// √(n/d) = √(n*d) / d for d>0. To get scaleBits of precision, scale the
// radicand by 2^(2·scaleBits): then mpz_sqrt on (n·d·2^(2·scaleBits)) returns
// floor(√(n·d) · 2^scaleBits), and dividing by (d · 2^scaleBits) gives the
// rational sqrt to within 2^-scaleBits.
//
// We never trade speed for soundness — floor rounds *down*, ceil rounds *up*,
// always. The scaleBits knob only controls how tight the bound is.
static void scaledRoot(const mpq_class& p, unsigned scaleBits,
                       mpz_class& outRoot, mpz_class& outScaledDen,
                       bool& outExact) {
    mpz_class n = p.get_num();
    mpz_class d = p.get_den();
    mpz_class scaleSq;
    mpz_ui_pow_ui(scaleSq.get_mpz_t(), 2, 2 * scaleBits);
    mpz_class M = n * d * scaleSq;
    mpz_sqrt(outRoot.get_mpz_t(), M.get_mpz_t());
    outExact = (outRoot * outRoot == M);
    mpz_class scale;
    mpz_ui_pow_ui(scale.get_mpz_t(), 2, scaleBits);
    outScaledDen = d * scale;
}

mpq_class mpqSqrtFloor(const mpq_class& p, unsigned scaleBits) {
    if (p <= 0) return mpq_class(0);
    mpz_class root, scaledDen;
    bool exact = false;
    scaledRoot(p, scaleBits, root, scaledDen, exact);
    // root ≤ √(n·d) · 2^scaleBits, so root / (d · 2^scaleBits) ≤ √(n/d).
    mpq_class r(root, scaledDen);
    r.canonicalize();
    return r;
}

mpq_class mpqSqrtCeil(const mpq_class& p, unsigned scaleBits) {
    if (p <= 0) return mpq_class(0);
    mpz_class root, scaledDen;
    bool exact = false;
    scaledRoot(p, scaleBits, root, scaledDen, exact);
    if (!exact) ++root;
    // root ≥ √(n·d) · 2^scaleBits (by the +1 when inexact, else exact).
    mpq_class r(root, scaledDen);
    r.canonicalize();
    return r;
}

} // namespace xolver
