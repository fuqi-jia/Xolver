#include "theory/arith/linearizer/MonomialBoundGenerator.h"
#include <algorithm>

namespace xolver {

mpq_class MonomialBoundGenerator::powQ(const mpq_class& base, int exponent) {
    mpq_class r = 1;
    for (int i = 0; i < exponent; ++i) r *= base;
    return r;
}

// ---------------------------------------------------------------------------
// factorRange: tight numeric range of x^e over the box [l, u].
// ---------------------------------------------------------------------------
std::optional<std::pair<mpq_class, mpq_class>>
MonomialBoundGenerator::factorRange(const Factor& f) {
    if (!f.bounds.isFinite()) return std::nullopt;
    const mpq_class& l = f.bounds.lower;
    const mpq_class& u = f.bounds.upper;
    const int e = f.exponent;
    if (e <= 0) return std::nullopt;          // not a polynomial exponent we handle

    mpq_class lE = powQ(l, e);
    mpq_class uE = powQ(u, e);

    if ((e % 2) == 0) {
        // x^e is convex with a minimum at x = 0.
        if (l > 0 || u < 0) {
            // Interval avoids 0, x^e is monotone (increasing if l>0,
            // decreasing if u<0). The min/max are at endpoints.
            mpq_class lo = std::min(lE, uE);
            mpq_class hi = std::max(lE, uE);
            return std::make_pair(lo, hi);
        }
        // Interval contains 0: min = 0, max = max(|l|^e, |u|^e).
        mpq_class hi = std::max(lE, uE);   // both nonneg already
        return std::make_pair(mpq_class(0), hi);
    } else {
        // Odd exponent: x^e is strictly increasing on all of R.
        // Range is exactly [l^e, u^e].
        return std::make_pair(lE, uE);
    }
}

// ---------------------------------------------------------------------------
// productRange: sound interval product of per-factor ranges.
// All-or-nothing: missing range -> nullopt.
// ---------------------------------------------------------------------------
std::optional<std::pair<mpq_class, mpq_class>>
MonomialBoundGenerator::productRange(
    const mpq_class& coefficient,
    const std::vector<std::optional<std::pair<mpq_class, mpq_class>>>& perFactor) {
    mpq_class lo = coefficient;
    mpq_class hi = coefficient;
    for (const auto& opt : perFactor) {
        if (!opt) return std::nullopt;
        const auto& [fl, fh] = *opt;
        mpq_class c1 = lo * fl, c2 = lo * fh, c3 = hi * fl, c4 = hi * fh;
        mpq_class nl = std::min({c1, c2, c3, c4});
        mpq_class nh = std::max({c1, c2, c3, c4});
        lo = nl;
        hi = nh;
    }
    return std::make_pair(lo, hi);
}

// ---------------------------------------------------------------------------
// Main entry: generate up to 3 families of sound cuts on s = c·∏ x_i^{e_i}.
// ---------------------------------------------------------------------------
std::vector<LinearCut> MonomialBoundGenerator::generate(
    const AuxTerm& s,
    const mpq_class& coefficient,
    const std::vector<Factor>& factors,
    SatLit nonlinearReason,
    const Options& opt,
    SortKind sort) {

    std::vector<LinearCut> cuts;
    if (factors.size() < 2) return cuts;   // <2 factors -> covered by Power/Square/Product
    if (coefficient == 0) return cuts;     // s = 0 trivially; LRA layer prunes elsewhere

    // ------------------------------------------------------------------
    // Step 0: gather per-factor ranges and the union of all reasons.
    // ------------------------------------------------------------------
    std::vector<std::optional<std::pair<mpq_class, mpq_class>>> ranges;
    ranges.reserve(factors.size());
    std::vector<SatLit> reasonsAll{nonlinearReason};
    for (const auto& f : factors) {
        ranges.push_back(factorRange(f));
        if (!f.bounds.lowerReasons.empty())
            reasonsAll.insert(reasonsAll.end(),
                              f.bounds.lowerReasons.begin(),
                              f.bounds.lowerReasons.end());
        if (!f.bounds.upperReasons.empty())
            reasonsAll.insert(reasonsAll.end(),
                              f.bounds.upperReasons.begin(),
                              f.bounds.upperReasons.end());
    }
    // ------------------------------------------------------------------
    // Family 0: sign-only cuts (NEW). Fires even when factors lack upper
    // bounds — only requires each factor to be sign-pinned (lower > 0
    // OR upper < 0 with odd exponent collapsing the sign). This was the
    // hole my Phase 2 generator had: every mgc-style benchmark has
    // strictly-positive vars with no upper bound, so the previous code
    // emitted zero cuts. cvc5's ARITH_NL_COMPARISON sits at this layer.
    //
    // Soundness: for each factor, even exponent ⇒ x^e ≥ 0 always; odd
    // exponent ⇒ sign(x^e) = sign(x), strict-pinned to sign(lower) when
    // lower > 0 (the only one-sided case the cut needs). Combined with
    // coefficient sign, the monomial's strict sign is determined.
    // Emit `s > 0` (as `-s < 0`) or `s < 0` (as `s < 0`).
    if (opt.emitSignOnly) {
        int monoSign = (coefficient > 0) ? 1 : (coefficient < 0 ? -1 : 0);
        bool signPinned = (monoSign != 0);
        std::vector<SatLit> signReasons{nonlinearReason};
        for (const auto& f : factors) {
            if (!signPinned) break;
            int factorSign;
            const bool eEven = (f.exponent % 2) == 0;
            if (f.bounds.hasLower && f.bounds.lower > 0) {
                // x > 0 ⇒ x^e > 0 regardless of parity.
                factorSign = 1;
                signReasons.insert(signReasons.end(),
                                   f.bounds.lowerReasons.begin(),
                                   f.bounds.lowerReasons.end());
            } else if (f.bounds.hasUpper && f.bounds.upper < 0) {
                // x < 0 ⇒ x^e > 0 if even, < 0 if odd.
                factorSign = eEven ? 1 : -1;
                signReasons.insert(signReasons.end(),
                                   f.bounds.upperReasons.begin(),
                                   f.bounds.upperReasons.end());
            } else if (eEven) {
                // Even exponent and sign-unpinned: x^e ≥ 0, but could be 0
                // at x = 0. The MONOMIAL becomes non-strict (≥ 0 or ≤ 0),
                // which the strict `<` cut doesn't capture. Drop this case
                // to keep the cut strict and sound.
                signPinned = false;
                break;
            } else {
                // Odd exponent without sign-pinned bound ⇒ no sign info.
                signPinned = false;
                break;
            }
            monoSign *= factorSign;
        }
        if (signPinned && monoSign != 0) {
            // monoSign > 0 ⇒ s > 0 ⇒ `-s < 0`; monoSign < 0 ⇒ s < 0.
            ZeroLinearConstraint z;
            z.expr.terms.push_back({s.name, mpq_class(monoSign > 0 ? -1 : 1)});
            z.expr.constant = 0;
            z.rel = Relation::Lt;
            z.sort = sort;
            z.debugTag = "mono_sign_only";
            cuts.push_back({std::move(z), signReasons, "mono_sign_only"});
        }
    }

    // Without finite ranges on every factor, the three numeric families
    // can't produce a sound bound. Family 0 above doesn't depend on
    // ranges so it's already emitted; this gate only blocks Families 1-3.
    for (const auto& r : ranges) if (!r) return cuts;

    auto totalRange = productRange(coefficient, ranges);
    if (!totalRange) return cuts;
    const mpq_class& sLo = totalRange->first;
    const mpq_class& sHi = totalRange->second;

    // ------------------------------------------------------------------
    // Family 1: interval envelope  sLo <= s <= sHi
    //   Emitted as two cuts:
    //      sLo - s <= 0   (lower bound)
    //      s - sHi <= 0   (upper bound)
    // ------------------------------------------------------------------
    if (opt.emitInterval) {
        {
            ZeroLinearConstraint z;
            z.expr.terms.push_back({s.name, mpq_class(-1)});
            z.expr.constant = sLo;
            z.rel = Relation::Leq;
            z.sort = sort;
            z.debugTag = "mono_interval_lower";
            cuts.push_back({std::move(z), reasonsAll, "mono_interval_lower"});
        }
        if (cuts.size() < opt.maxCutsHere) {
            ZeroLinearConstraint z;
            z.expr.terms.push_back({s.name, mpq_class(1)});
            z.expr.constant = -sHi;
            z.rel = Relation::Leq;
            z.sort = sort;
            z.debugTag = "mono_interval_upper";
            cuts.push_back({std::move(z), reasonsAll, "mono_interval_upper"});
        }
    }

    // ------------------------------------------------------------------
    // Family 2: pivot-corner secants.
    //   For each pivot factor k with finite l_k != u_k:
    //     R = c · ∏_{i != k} x_i^{e_i} has range [R_lo, R_hi]
    //     x_k^{e_k} ranges over [P_lo, P_hi]; on the pivot's branch we
    //     can replace x_k^{e_k} by its chord at endpoints l_k, u_k:
    //          P_lin(x_k) = ((u_k^{e_k} - l_k^{e_k}) / (u_k - l_k)) (x_k - l_k)
    //                     + l_k^{e_k}
    //     P_lin lies *between* P and its chord; specifically
    //          - if x_k^{e_k} is convex on [l_k, u_k]: x_k^{e_k} <= P_lin
    //          - if concave: x_k^{e_k} >= P_lin
    //     so multiplying by R's sign-known range gives a sound linear
    //     relaxation. For mixed-sign R or e_k==1 we skip — those cases
    //     are handled by McCormickGenerator or the sign-only path.
    // ------------------------------------------------------------------
    if (opt.emitPivotCorner && cuts.size() < opt.maxCutsHere) {
        for (size_t k = 0; k < factors.size(); ++k) {
            if (cuts.size() >= opt.maxCutsHere) break;
            const Factor& fk = factors[k];
            if (fk.exponent <= 1) continue;
            const mpq_class& lk = fk.bounds.lower;
            const mpq_class& uk = fk.bounds.upper;
            if (lk == uk) continue;

            // Range of x_k^{e_k}. Convex iff even exponent OR lk >= 0.
            const bool nIsEven = (fk.exponent % 2) == 0;
            const bool branchPureConvex = nIsEven || lk >= 0;
            const bool branchPureConcave = !nIsEven && uk <= 0;
            if (!branchPureConvex && !branchPureConcave) continue; // mixed sign for odd

            // R = c · ∏_{i != k}.
            std::vector<std::optional<std::pair<mpq_class, mpq_class>>> rest;
            rest.reserve(factors.size() - 1);
            for (size_t i = 0; i < factors.size(); ++i)
                if (i != k) rest.push_back(ranges[i]);
            auto rRange = productRange(coefficient, rest);
            if (!rRange) continue;
            const mpq_class& Rlo = rRange->first;
            const mpq_class& Rhi = rRange->second;

            // chord(P) = slope * (x_k - lk) + l_k^{e_k}
            mpq_class lkE = powQ(lk, fk.exponent);
            mpq_class ukE = powQ(uk, fk.exponent);
            mpq_class slopeP = (ukE - lkE) / (uk - lk);
            // intercept at x_k = lk is lkE; full form chord(x_k) = slopeP*x_k + (lkE - slopeP*lk)

            // Case analysis on sign(R). For sound linear cut, we need a
            // single multiplicative sign for R; if R straddles zero
            // (Rlo<0<Rhi), neither side gives a tight cut without an
            // additional split, so skip.
            const bool R_nonneg = Rlo >= 0;
            const bool R_nonpos = Rhi <= 0;
            if (!R_nonneg && !R_nonpos) continue;

            //   R >= 0 case:
            //     branchConvex:   x_k^{e_k} <= chord(x_k)   =>  s <= Rhi * chord(x_k)
            //                                                 s >= Rlo * x_k^{e_k}_min_at_box (already in family 1)
            //     branchConcave: x_k^{e_k} >= chord(x_k)   =>  s >= Rlo * chord(x_k)
            //   R <= 0 case:
            //     branchConvex:   s >= Rlo * chord(x_k)  (Rlo<=0 flips inequality)
            //     branchConcave:  s <= Rhi * chord(x_k)  (Rhi<=0)
            //
            // Encode as a single ZeroLinearConstraint <expr> <= 0.
            //
            //   chord(x_k) = slopeP * x_k + (lkE - slopeP*lk)
            //   K * chord(x_k) = K*slopeP * x_k + K*(lkE - slopeP*lk)
            //   "s <= K * chord":  s - K*slopeP * x_k - K*(lkE - slopeP*lk) <= 0
            //   "s >= K * chord": -s + K*slopeP * x_k + K*(lkE - slopeP*lk) <= 0
            auto emit = [&](const mpq_class& K, bool sUpper, const char* tag) {
                if (cuts.size() >= opt.maxCutsHere) return;
                mpq_class chordSlope = K * slopeP;
                mpq_class chordConst = K * (lkE - slopeP * lk);
                ZeroLinearConstraint z;
                if (sUpper) {
                    z.expr.terms.push_back({s.name, mpq_class(1)});
                    z.expr.terms.push_back({fk.var, -chordSlope});
                    z.expr.constant = -chordConst;
                } else {
                    z.expr.terms.push_back({s.name, mpq_class(-1)});
                    z.expr.terms.push_back({fk.var, chordSlope});
                    z.expr.constant = chordConst;
                }
                z.rel = Relation::Leq;
                z.sort = sort;
                z.debugTag = tag;
                cuts.push_back({std::move(z), reasonsAll, tag});
            };

            if (R_nonneg) {
                if (branchPureConvex)  emit(Rhi, /*sUpper=*/true,  "mono_pivot_R_pos_convex_upper");
                if (branchPureConcave) emit(Rlo, /*sUpper=*/false, "mono_pivot_R_pos_concave_lower");
            } else { // R_nonpos
                if (branchPureConvex)  emit(Rlo, /*sUpper=*/false, "mono_pivot_R_neg_convex_lower");
                if (branchPureConcave) emit(Rhi, /*sUpper=*/true,  "mono_pivot_R_neg_concave_upper");
            }
        }
    }

    // ------------------------------------------------------------------
    // Family 3: multi-variable tangent at model point (all-nonneg case).
    //   f(x) = c · ∏ x_i^{e_i}, restricted to factors that all have
    //   l_i >= 0 (so every x_i^{e_i} is convex in x_i and the product
    //   is sign-monotone in each variable on the relevant orthant).
    //
    //   ∂f/∂x_j (m) = c · e_j · m_j^{e_j - 1} · ∏_{i != j} m_i^{e_i}
    //              = (e_j / m_j) · f(m)               (when m_j != 0)
    //
    //   Tangent hyperplane T(x) = f(m) + Σ (∂f/∂x_j)(m) (x_j - m_j).
    //   Each x_i^{e_i} is convex in x_i on [0, inf), so by convexity
    //   along axes T(x) <= f(x) when every x_i >= 0 and *m* is feasible
    //   (m_i >= 0). Hence  s >= T(x)  is sound.
    //
    //   Encoded as:   -s + Σ ∂_j f(m) · x_j + (f(m) - Σ ∂_j f(m) · m_j) <= 0
    // ------------------------------------------------------------------
    if (opt.emitTangentPlane && cuts.size() < opt.maxCutsHere) {
        bool allPosBranch = true;
        std::vector<mpq_class> m;
        m.reserve(factors.size());
        for (const auto& f : factors) {
            if (!f.bounds.hasLower || f.bounds.lower < 0) {
                allPosBranch = false; break;
            }
            // model value required and strictly positive (so derivative
            // is finite and tangent useful). Fall back to lower bound
            // if model missing, midpoint if both bounds finite.
            mpq_class mv;
            if (f.modelVal && *f.modelVal > 0) mv = *f.modelVal;
            else if (f.bounds.lower > 0)       mv = f.bounds.lower;
            else                               mv = (f.bounds.lower + f.bounds.upper) / 2;
            if (mv <= 0) { allPosBranch = false; break; }
            m.push_back(mv);
        }
        if (allPosBranch && m.size() == factors.size()) {
            mpq_class fm = coefficient;
            for (size_t i = 0; i < factors.size(); ++i)
                fm *= powQ(m[i], factors[i].exponent);

            // For sound LOWER bound via convexity, we need the coefficient
            // sign: if coefficient < 0, the product is concave in the
            // positive orthant and the tangent is an UPPER bound instead.
            const bool coefPos = coefficient > 0;

            std::vector<mpq_class> grad;
            grad.reserve(factors.size());
            for (size_t j = 0; j < factors.size(); ++j) {
                // grad_j = (e_j / m_j) * f(m); guaranteed m_j > 0.
                grad.push_back(mpq_class(factors[j].exponent) * fm / m[j]);
            }
            mpq_class constShift = fm;
            for (size_t j = 0; j < factors.size(); ++j) {
                constShift -= grad[j] * m[j];
            }

            ZeroLinearConstraint z;
            if (coefPos) {
                // s >= T(x):  -s + Σ grad_j x_j + constShift <= 0
                z.expr.terms.push_back({s.name, mpq_class(-1)});
                for (size_t j = 0; j < factors.size(); ++j)
                    z.expr.terms.push_back({factors[j].var, grad[j]});
                z.expr.constant = constShift;
                z.rel = Relation::Leq;
                z.debugTag = "mono_tangent_lower";
            } else {
                // s <= T(x):  s - Σ grad_j x_j - constShift <= 0
                z.expr.terms.push_back({s.name, mpq_class(1)});
                for (size_t j = 0; j < factors.size(); ++j)
                    z.expr.terms.push_back({factors[j].var, -grad[j]});
                z.expr.constant = -constShift;
                z.rel = Relation::Leq;
                z.debugTag = "mono_tangent_upper";
            }
            z.sort = sort;
            cuts.push_back({std::move(z), reasonsAll, z.debugTag});
        }
    }

    return cuts;
}

} // namespace xolver
