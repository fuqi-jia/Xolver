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

// Generalized version of scaledRoot for arbitrary d ≥ 1:
//   p = n / D, p^(1/d) = (n · D^(d-1))^(1/d) / D.
// We scale the radicand by 2^(d · scaleBits): then
//   mpz_root(n · D^(d-1) · 2^(d·scaleBits), d) = floor((n · D^(d-1))^(1/d) · 2^scaleBits),
// and dividing by D · 2^scaleBits recovers the rational d-th root to within
// 2^-scaleBits precision. Exactness check: root^d == M.
static void scaledRootD(const mpq_class& p, unsigned d, unsigned scaleBits,
                        mpz_class& outRoot, mpz_class& outScaledDen,
                        bool& outExact) {
    mpz_class n = p.get_num();
    mpz_class D = p.get_den();

    // D^(d-1)
    mpz_class Dpow;
    mpz_pow_ui(Dpow.get_mpz_t(), D.get_mpz_t(), d - 1);

    // 2^(d · scaleBits)
    mpz_class scalePow;
    mpz_ui_pow_ui(scalePow.get_mpz_t(), 2, d * scaleBits);

    mpz_class M = n * Dpow * scalePow;
    mpz_root(outRoot.get_mpz_t(), M.get_mpz_t(), d);

    // Exactness: root^d == M.
    mpz_class rootPow;
    mpz_pow_ui(rootPow.get_mpz_t(), outRoot.get_mpz_t(), d);
    outExact = (rootPow == M);

    // Denominator is D · 2^scaleBits.
    mpz_class scale;
    mpz_ui_pow_ui(scale.get_mpz_t(), 2, scaleBits);
    outScaledDen = D * scale;
}

mpq_class mpqRootFloor(const mpq_class& p, unsigned d, unsigned scaleBits) {
    if (d == 0) return mpq_class(0);  // defensive — 0-th root undefined
    if (d == 1) return p;
    if (p <= 0) return mpq_class(0);
    if (d == 2) return mpqSqrtFloor(p, scaleBits);

    mpz_class root, scaledDen;
    bool exact = false;
    scaledRootD(p, d, scaleBits, root, scaledDen, exact);
    mpq_class r(root, scaledDen);
    r.canonicalize();
    return r;
}

mpq_class mpqRootCeil(const mpq_class& p, unsigned d, unsigned scaleBits) {
    if (d == 0) return mpq_class(0);
    if (d == 1) return p;
    if (p <= 0) return mpq_class(0);
    if (d == 2) return mpqSqrtCeil(p, scaleBits);

    mpz_class root, scaledDen;
    bool exact = false;
    scaledRootD(p, d, scaleBits, root, scaledDen, exact);
    if (!exact) ++root;
    mpq_class r(root, scaledDen);
    r.canonicalize();
    return r;
}

} // namespace xolver
