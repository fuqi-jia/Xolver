#include "theory/arith/kernel/icp/contractors/RelationContractorQ.h"
#include "theory/arith/kernel/interval/IntervalQOps.h"
#include "theory/arith/kernel/interval/IntervalQRoots.h"
#include <algorithm>

namespace xolver {

RelationContractorQ::RelationContractorQ(const IcpConstraint& constraint, PolynomialKernel& kernel)
    : constraint_(constraint), kernel_(kernel) {
    vars_ = kernel_.variables(constraint_.poly);
}

ContractorResultQ RelationContractorQ::contract(ReasonedBoxQ& box) {
    // Univariate safeguard — multi-var requires corner enumeration which
    // explodes and is the linearizer's job, not ICP V1.
    if (vars_.size() != 1) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const std::string& var = vars_[0];
    auto riOpt = box.get(var);
    if (!riOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto degOpt = kernel_.degree(constraint_.poly, var);
    if (!degOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint_.poly, var);
    if (!coeffsOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const auto& coeffs = *coeffsOpt;
    const IntervalQ& xInterval = riOpt->interval;

    // Horner-style interval evaluation: Σ c_i · x^{deg-i}.
    // Reusing intervalQAdd/Mul/Pow — each is a sound over-approx.
    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (size_t i = 0; i < coeffs.size(); ++i) {
        const mpz_class& coeff = coeffs[i];
        if (coeff == 0) continue;
        size_t power = coeffs.size() - 1 - i;
        IntervalQ termInterval = intervalQPow(xInterval, static_cast<uint32_t>(power));
        if (coeff != 1) {
            mpq_class coeffQ(coeff);
            IntervalQ coeffInterval{coeffQ, coeffQ};
            termInterval = intervalQMul(coeffInterval, termInterval);
        }
        result = intervalQAdd(result, termInterval);
    }

    // Reasons combine the box's bound reasons with the constraint reason —
    // both are needed to make the conflict explanation sound.
    std::vector<SatLit> reasons = riOpt->reasons;
    reasons.push_back(constraint_.reason);

    if (isDefinitelyViolated(result, constraint_.rel)) {
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{reasons},
            {}
        };
    }

    // V2 — quadratic inversion narrowing. The derived [r1Lo, r2Hi] depends
    // only on the polynomial (not on the current box), so the constraint
    // reason alone justifies the raw feasible-set bound; the box bound
    // reasons enter only via the intersection step below. We pass the
    // already-built `reasons` (box ∪ constraint) to BoundUpdateQ — coarser
    // than minimal but always sound.
    auto narrowedOpt = tryNarrowDeg2(coeffs, constraint_.rel);
    if (narrowedOpt) {
        const IntervalQ& narrowed = *narrowedOpt;
        if (narrowed.isEmpty()) {
            // disc < 0: ax²+bx+c > 0 everywhere (a > 0); Leq/Lt unsatisfiable.
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        mpq_class newLo = std::max(xInterval.lo, narrowed.lo);
        mpq_class newHi = std::min(xInterval.hi, narrowed.hi);
        if (newLo > newHi) {
            // Intersection of box with feasible set is empty → conflict.
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        if (newLo != xInterval.lo || newHi != xInterval.hi) {
            IntervalQ newI{newLo, newHi};
            box.narrow(var, newI, reasons);
            BoundUpdateQ update{var, newI, reasons};
            return ContractorResultQ{
                IcpStatus::DomainUpdate,
                std::nullopt,
                {update}
            };
        }
    }

    // V3a — pure-monomial sign narrowing (degree d ≥ 3). Mutually exclusive
    // with V2's degree-2 path (V2 returns DomainUpdate or Conflict and
    // short-circuits before we get here when applicable; we only reach V3
    // if V2 returned nullopt — i.e., this is not a degree-2 trinomial).
    auto monomialOpt = tryNarrowPureMonomial(coeffs, constraint_.rel, xInterval);
    if (monomialOpt) {
        const IntervalQ& newI = *monomialOpt;
        if (newI.isEmpty()) {
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        if (newI.lo != xInterval.lo || newI.hi != xInterval.hi) {
            box.narrow(var, newI, reasons);
            BoundUpdateQ update{var, newI, reasons};
            return ContractorResultQ{
                IcpStatus::DomainUpdate,
                std::nullopt,
                {update}
            };
        }
    }

    // V3b — monomial + constant via rational d-th root (d ≥ 3, c ≠ 0).
    // Same return-contract as V3a (interval already intersected with xBox).
    auto monConstOpt = tryNarrowMonomialPlusConst(coeffs, constraint_.rel, xInterval);
    if (monConstOpt) {
        const IntervalQ& newI = *monConstOpt;
        if (newI.isEmpty()) {
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        if (newI.lo != xInterval.lo || newI.hi != xInterval.hi) {
            box.narrow(var, newI, reasons);
            BoundUpdateQ update{var, newI, reasons};
            return ContractorResultQ{
                IcpStatus::DomainUpdate,
                std::nullopt,
                {update}
            };
        }
    }

    // V5e — sparse-pair Eq narrowing for `a·x^d + b·x^(d-p) = 0`. Tighter
    // than V5d's Cauchy for this exact shape. Eq only; Leq/Geq fall
    // through to V5d.
    auto sparsePairOpt = tryNarrowSparseMonomialPair(coeffs, constraint_.rel, xInterval);
    if (sparsePairOpt) {
        const IntervalQ& newI = *sparsePairOpt;
        if (newI.isEmpty()) {
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        if (newI.lo != xInterval.lo || newI.hi != xInterval.hi) {
            box.narrow(var, newI, reasons);
            BoundUpdateQ update{var, newI, reasons};
            return ContractorResultQ{
                IcpStatus::DomainUpdate,
                std::nullopt,
                {update}
            };
        }
    }

    // V5d — Cauchy bound on real roots for dense mixed-degree univariate.
    // Fires only when V2/V3a/V3b/V5e declined. Loose but sound.
    auto cauchyOpt = tryNarrowCauchyBracket(coeffs, constraint_.rel, xInterval);
    if (cauchyOpt) {
        const IntervalQ& newI = *cauchyOpt;
        if (newI.isEmpty()) {
            return ContractorResultQ{
                IcpStatus::Conflict,
                TheoryConflict{reasons},
                {}
            };
        }
        if (newI.lo != xInterval.lo || newI.hi != xInterval.hi) {
            box.narrow(var, newI, reasons);
            BoundUpdateQ update{var, newI, reasons};
            return ContractorResultQ{
                IcpStatus::DomainUpdate,
                std::nullopt,
                {update}
            };
        }
    }

    return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
}

std::vector<std::string> RelationContractorQ::vars() const {
    return vars_;
}

SatLit RelationContractorQ::reason() const {
    return constraint_.reason;
}

bool RelationContractorQ::isDefinitelyViolated(const IntervalQ& polyInterval, Relation rel) const {
    // Over reals, intervals are closed [lo, hi] — strict relations need strict
    // sign separation, non-strict need non-strict separation. Each branch is the
    // contrapositive of "∃ value in interval satisfying rel"; if no value
    // satisfies, the asserted rel is impossible on this box → Conflict.
    switch (rel) {
        case Relation::Leq:
            // p ≤ 0 violated if every p in interval is > 0.
            return polyInterval.lo > 0;
        case Relation::Geq:
            // p ≥ 0 violated if every p in interval is < 0.
            return polyInterval.hi < 0;
        case Relation::Lt:
            // p < 0 violated if every p in interval is ≥ 0.
            return polyInterval.lo >= 0;
        case Relation::Gt:
            // p > 0 violated if every p in interval is ≤ 0.
            return polyInterval.hi <= 0;
        case Relation::Eq:
            // p = 0 violated if 0 ∉ interval.
            return !polyInterval.containsZero();
        case Relation::Neq:
            // p ≠ 0 violated if interval = {0}.
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false;
    }
}

std::optional<IntervalQ> RelationContractorQ::tryNarrowDeg2(
        const std::vector<mpz_class>& coeffs, Relation rel) const {
    // V2 scope: Leq/Lt (single closed interval when a > 0) and Eq (closed
    // bracket containing the two roots). Eq is sign-invariant so we can
    // normalize a > 0 by negating all coefficients.
    if (rel != Relation::Leq && rel != Relation::Lt && rel != Relation::Eq) {
        return std::nullopt;
    }
    if (coeffs.size() != 3) {
        return std::nullopt;
    }

    mpz_class a = coeffs[0];
    mpz_class b = coeffs[1];
    mpz_class c = coeffs[2];

    if (a == 0) {
        // Defensive: degree-2 invariant was broken.
        return std::nullopt;
    }

    if (a < 0) {
        // Leq/Lt with a < 0 is a union of unbounded sets — skip.
        // Eq is sign-invariant: negate all coefficients to renormalize a > 0.
        if (rel != Relation::Eq) return std::nullopt;
        a = -a;
        b = -b;
        c = -c;
    }

    // disc = b² − 4ac (integer arithmetic).
    mpz_class disc = b * b - 4 * a * c;

    if (disc < 0) {
        // No real roots, parabola entirely above 0 ⇒ Leq/Lt/Eq impossible.
        // Signal via an empty interval; caller converts to Conflict.
        return IntervalQ{mpq_class(1), mpq_class(0)};
    }

    // Outward sqrt: sqrtDisc ≥ √disc. With 2a > 0 the order is preserved
    // when we divide, so r1Lo ≤ true_r1 and r2Hi ≥ true_r2 — the returned
    // interval is a superset of the true feasible set:
    //   Leq/Lt: [r1, r2] (parabola dips below 0 between the roots)
    //   Eq:     {r1, r2} ⊂ [r1, r2] (closed bracket over-approx)
    mpq_class sqrtDisc = mpqSqrtCeil(mpq_class(disc));

    mpq_class twoA(2 * a);
    mpq_class r1Lo = (mpq_class(-b) - sqrtDisc) / twoA;
    mpq_class r2Hi = (mpq_class(-b) + sqrtDisc) / twoA;
    r1Lo.canonicalize();
    r2Hi.canonicalize();

    return IntervalQ{r1Lo, r2Hi};
}

namespace {

// Flip `r` so that the predicate `p rel 0` becomes equivalent after negating
// p. Used to normalize the leading coefficient sign in pure-monomial
// reasoning. Eq/Neq are sign-invariant.
Relation flipSign(Relation r) {
    switch (r) {
        case Relation::Leq: return Relation::Geq;
        case Relation::Geq: return Relation::Leq;
        case Relation::Lt:  return Relation::Gt;
        case Relation::Gt:  return Relation::Lt;
        default:            return r;
    }
}

} // namespace

std::optional<IntervalQ> RelationContractorQ::tryNarrowPureMonomial(
        const std::vector<mpz_class>& coeffs, Relation rel,
        const IntervalQ& xBox) const {
    // V3a scope: degree d ≥ 3. V2's discriminant path strictly dominates for
    // d == 2, so we don't compete on that case.
    if (coeffs.size() < 4) return std::nullopt;

    if (coeffs[0] == 0) return std::nullopt;  // defensive: leading-coeff invariant

    // All non-leading coefficients must be zero (pure monomial a·x^d).
    for (size_t i = 1; i < coeffs.size(); ++i) {
        if (coeffs[i] != 0) return std::nullopt;
    }

    size_t d = coeffs.size() - 1;
    bool aPositive = (coeffs[0] > 0);

    // Normalize a > 0 by flipping the relation when negating. Eq/Neq pass
    // through (multiplying both sides by -1 preserves equality predicates).
    Relation r = aPositive ? rel : flipSign(rel);

    const mpq_class kZero(0);
    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    if (d % 2 == 0) {
        // Even d ≥ 4: x^d ≥ 0, with strict equality only at x = 0.
        switch (r) {
            case Relation::Leq:
            case Relation::Eq:
                // {x : x^d ≤ 0} = {0}; intersect with xBox.
                return xBox.contains(kZero)
                    ? IntervalQ{kZero, kZero}
                    : kEmpty;
            case Relation::Lt:
                // x^d < 0 unsatisfiable (a > 0, d even).
                return kEmpty;
            case Relation::Geq:
                // x^d ≥ 0 vacuously true; nothing to narrow.
                return std::nullopt;
            case Relation::Gt:
            case Relation::Neq:
                // {x : x ≠ 0} ∩ xBox is two pieces when xBox straddles 0,
                // not representable as a single IntervalQ — skip.
                return std::nullopt;
            default:
                return std::nullopt;
        }
    } else {
        // Odd d ≥ 3: sign(x^d) = sign(x), so feasibility reduces to a
        // sign condition on x itself. Strict relations (Lt, Gt) get a
        // closed over-approximation (admitting x = 0) — sound: we never
        // drop a strict solution, only delay conflict detection by an
        // iteration when the box collapses to {0}.
        switch (r) {
            case Relation::Leq:
            case Relation::Lt: {
                mpq_class newHi = std::min(xBox.hi, kZero);
                if (xBox.lo > newHi) return kEmpty;
                return IntervalQ{xBox.lo, newHi};
            }
            case Relation::Geq:
            case Relation::Gt: {
                mpq_class newLo = std::max(xBox.lo, kZero);
                if (newLo > xBox.hi) return kEmpty;
                return IntervalQ{newLo, xBox.hi};
            }
            case Relation::Eq:
                return xBox.contains(kZero)
                    ? IntervalQ{kZero, kZero}
                    : kEmpty;
            case Relation::Neq:
                // Same single-interval limitation as the even-d case.
                return std::nullopt;
            default:
                return std::nullopt;
        }
    }
}

std::optional<IntervalQ> RelationContractorQ::tryNarrowMonomialPlusConst(
        const std::vector<mpz_class>& coeffs, Relation rel,
        const IntervalQ& xBox) const {
    if (coeffs.size() < 4) return std::nullopt;  // d ≥ 3 (V2 handles d=2)
    if (coeffs[0] == 0) return std::nullopt;

    // Shape: a·x^d + c (intermediate coefficients are all zero).
    for (size_t i = 1; i + 1 < coeffs.size(); ++i) {
        if (coeffs[i] != 0) return std::nullopt;
    }
    const mpz_class& c = coeffs.back();
    if (c == 0) return std::nullopt;  // V3a's territory

    unsigned d = static_cast<unsigned>(coeffs.size() - 1);
    const mpz_class& a = coeffs[0];

    // Normalize a > 0 by flipping rel when negating.
    bool aPositive = (a > 0);
    Relation r = aPositive ? rel : flipSign(rel);

    // T = -c/a (the same expression in both branches; we build it from
    // positive components to keep mpq's invariant that den > 0).
    mpq_class T = aPositive ? mpq_class(-c, a)
                            : mpq_class(c, -a);
    T.canonicalize();

    const mpq_class kZero(0);
    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    // Outward d-th root helpers that handle arbitrary-sign T. For T < 0 with
    // odd d (the only meaningful case), negation flips floor and ceil.
    auto rootCeil = [d](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootCeil(t, d);
        return -mpqRootFloor(-t, d);
    };
    auto rootFloor = [d](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootFloor(t, d);
        return -mpqRootCeil(-t, d);
    };

    bool dEven = (d % 2 == 0);

    if (dEven) {
        if (T < 0) {
            // x^d ≥ 0 > T: Leq/Lt/Eq unsat; Geq/Gt/Neq vacuous.
            switch (r) {
                case Relation::Leq:
                case Relation::Lt:
                case Relation::Eq:
                    return kEmpty;
                default:
                    return std::nullopt;
            }
        }
        // T ≥ 0 — bidirectional bound via T^(1/d).
        switch (r) {
            case Relation::Leq:
            case Relation::Lt:
            case Relation::Eq: {
                // Leq/Lt: x^d ≤ T ⇔ x ∈ [-T^(1/d), T^(1/d)].
                // Eq:     x^d = T ⇒ x ∈ {-T^(1/d), T^(1/d)}, over-approxed by
                //         the same closed bracket.
                mpq_class rt = rootCeil(T);  // upper bound rounded UP
                mpq_class negRt(-rt);        // materialize the expression
                mpq_class lo = std::max(xBox.lo, negRt);
                mpq_class hi = std::min(xBox.hi, rt);
                if (lo > hi) return kEmpty;
                return IntervalQ{lo, hi};
            }
            case Relation::Geq:
            case Relation::Gt:
                // |x| ≥ T^(1/d) is a union of two unbounded sets ⇒ skip.
                return std::nullopt;
            case Relation::Neq:
                return std::nullopt;
            default:
                return std::nullopt;
        }
    }

    // d odd: x^d is strictly monotone.
    switch (r) {
        case Relation::Leq:
        case Relation::Lt: {
            mpq_class rt = rootCeil(T);  // closed over-approx of strict for Lt
            mpq_class hi = std::min(xBox.hi, rt);
            if (xBox.lo > hi) return kEmpty;
            return IntervalQ{xBox.lo, hi};
        }
        case Relation::Geq:
        case Relation::Gt: {
            mpq_class rt = rootFloor(T);
            mpq_class lo = std::max(xBox.lo, rt);
            if (lo > xBox.hi) return kEmpty;
            return IntervalQ{lo, xBox.hi};
        }
        case Relation::Eq: {
            mpq_class rLo = rootFloor(T);
            mpq_class rHi = rootCeil(T);
            mpq_class lo = std::max(xBox.lo, rLo);
            mpq_class hi = std::min(xBox.hi, rHi);
            if (lo > hi) return kEmpty;
            return IntervalQ{lo, hi};
        }
        case Relation::Neq:
            return std::nullopt;
        default:
            return std::nullopt;
    }
}

std::optional<IntervalQ> RelationContractorQ::tryNarrowSparseMonomialPair(
        const std::vector<mpz_class>& coeffs, Relation rel,
        const IntervalQ& xBox) const {
    // Shape: a·x^d + b·x^(d-p) rel 0  (constant = 0, exactly one
    // intermediate non-zero). Factor x^(d-p) · (a·x^p + b).
    // Eq: bracket via {0} ∪ roots-of-second-factor (tight).
    // Leq/Gt/Geq/Lt: parity case-split on k = d - p (the common-factor
    // exponent). Tighter than V5d Cauchy for these specific shapes.
    if (rel == Relation::Neq) return std::nullopt;
    if (coeffs.size() < 3) return std::nullopt;  // need degree ≥ 2
    if (coeffs[0] == 0) return std::nullopt;
    // Constant must be zero (V3b handles non-zero constant case tighter).
    if (coeffs.back() != 0) return std::nullopt;

    // Find exactly one intermediate non-zero. coeffs is stored
    // highest-degree-first: coeffs[i] is the coefficient of x^(d - i).
    int interIdx = -1;
    for (size_t i = 1; i + 1 < coeffs.size(); ++i) {
        if (coeffs[i] != 0) {
            if (interIdx >= 0) return std::nullopt;  // more than one intermediate
            interIdx = static_cast<int>(i);
        }
    }
    if (interIdx < 0) return std::nullopt;  // V3a's territory (pure monomial)

    // Factor: a·x^d + b·x^(d-p) = x^(d-p) · (a·x^p + b).
    //   coeffs[0]    ↔ a · x^d
    //   coeffs[idx]  ↔ b · x^(d-idx)     where idx = interIdx
    //   coeffs[end]  ↔ 0                 (required above)
    // So the common factor is x^(d-idx) and the second factor is a·x^idx + b
    // (degree idx). Below, p = degree of second factor; k = exponent of
    // common factor = d - p.
    unsigned p = static_cast<unsigned>(interIdx);
    unsigned d = static_cast<unsigned>(coeffs.size() - 1);
    unsigned k = d - p;

    // Sign-normalize: if a < 0, flip the relation and negate (a, b).
    // (Eq is sign-invariant; we just normalize T calculation.)
    mpz_class aNorm = coeffs[0];
    mpz_class bNorm = coeffs[interIdx];
    Relation rNorm = rel;
    if (aNorm < 0) {
        aNorm = -aNorm;
        bNorm = -bNorm;
        // flipSign on the relation (Eq passes through).
        switch (rNorm) {
            case Relation::Leq: rNorm = Relation::Geq; break;
            case Relation::Geq: rNorm = Relation::Leq; break;
            case Relation::Lt:  rNorm = Relation::Gt;  break;
            case Relation::Gt:  rNorm = Relation::Lt;  break;
            default: break;
        }
    }

    // T = -bNorm/aNorm with aNorm > 0.
    mpq_class T = mpq_class(-bNorm, aNorm);
    T.canonicalize();

    const mpq_class kZero(0);
    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    // Outward p-th root helpers (handle T < 0 via floor/ceil flip).
    auto rootCeil = [p](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootCeil(t, p);
        return -mpqRootFloor(-t, p);
    };
    auto rootFloor = [p](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootFloor(t, p);
        return -mpqRootCeil(-t, p);
    };

    bool pEven = (p % 2 == 0);
    bool kEven = (k % 2 == 0);

    auto intersect = [&](const mpq_class& lo, const mpq_class& hi) -> IntervalQ {
        mpq_class newLo = std::max(xBox.lo, lo);
        mpq_class newHi = std::min(xBox.hi, hi);
        if (newLo > newHi) return kEmpty;
        return IntervalQ{newLo, newHi};
    };

    // --- Eq branch ---------------------------------------------------------
    if (rNorm == Relation::Eq) {
        // Bracket starts at {0} (root from common factor x^k).
        mpq_class loBracket = kZero;
        mpq_class hiBracket = kZero;
        if (pEven) {
            if (T > 0) {
                mpq_class rtCeil = mpqRootCeil(T, p);
                mpq_class negRtCeil(-rtCeil);
                if (negRtCeil < loBracket) loBracket = negRtCeil;
                if (rtCeil > hiBracket) hiBracket = rtCeil;
            }
            // T == 0: x = 0 already in bracket.
            // T < 0: no real roots from second factor.
        } else {
            // p odd: single real root.
            mpq_class rtLo = rootFloor(T);
            mpq_class rtHi = rootCeil(T);
            if (rtLo < loBracket) loBracket = rtLo;
            if (rtHi > hiBracket) hiBracket = rtHi;
        }
        return intersect(loBracket, hiBracket);
    }

    // --- Leq/Lt branch (a > 0 normalized) ---------------------------------
    // Bracket of {x : x^k · g(x) ≤ 0} where g(x) = a·x^p + b. Strict Lt
    // uses the same closed over-approximation (sound — never drops a
    // strict solution).
    if (rNorm == Relation::Leq || rNorm == Relation::Lt) {
        if (kEven) {
            // x^k ≥ 0. Product ≤ 0 iff x = 0 OR g(x) ≤ 0.
            if (pEven) {
                if (T < 0) {
                    // g > 0 everywhere ⇒ only x = 0 satisfies.
                    return intersect(kZero, kZero);
                }
                // T ≥ 0: bracket [-rt, rt] (contains 0).
                mpq_class rtCeil = mpqRootCeil(T, p);
                mpq_class negRtCeil(-rtCeil);
                return intersect(negRtCeil, rtCeil);
            }
            // p odd: g ≤ 0 iff x ≤ rt. Union with {0}.
            mpq_class rtHi = rootCeil(T);
            // Over-approx: upper bound is max(rt, 0); lower is unbounded.
            mpq_class upper = (rtHi > kZero) ? rtHi : kZero;
            return intersect(xBox.lo, upper);
        }
        // k odd: product = x^k · g. Sign of x^k tracks sign of x.
        if (pEven) {
            if (T < 0) {
                // g > 0 always. Need x^k · g ≤ 0 ⇒ x^k ≤ 0 ⇒ x ≤ 0.
                return intersect(xBox.lo, kZero);
            }
            // T ≥ 0: g ≤ 0 in [-rt, rt]. Over-approx union: (-∞, rt].
            mpq_class rtCeil = mpqRootCeil(T, p);
            return intersect(xBox.lo, rtCeil);
        }
        // k odd, p odd: g ≤ 0 iff x ≤ rt; G+ = (0, rt] if rt > 0 else ∅;
        //               G- = [rt, 0) if rt < 0 else ∅. Plus {0}.
        if (T > 0) {
            // rt > 0. Bracket [0, rt].
            mpq_class rtCeil = mpqRootCeil(T, p);
            return intersect(kZero, rtCeil);
        }
        if (T < 0) {
            // rt < 0. Bracket [rt, 0].
            mpq_class rtLo = rootFloor(T);
            return intersect(rtLo, kZero);
        }
        // T == 0: bracket {0}.
        return intersect(kZero, kZero);
    }

    // --- Geq/Gt branch (a > 0 normalized) ---------------------------------
    // Bracket of {x : x^k · g(x) ≥ 0}. Many sub-cases produce no narrowing
    // (union covering all of ℝ); we return nullopt for those so V5d's
    // Cauchy fallback can try.
    if (rNorm == Relation::Geq || rNorm == Relation::Gt) {
        if (kEven) {
            if (pEven) {
                // T < 0: g > 0 always ⇒ all of ℝ. No narrowing.
                // T ≥ 0: union of unbounded regions + {0}. No narrowing.
                return std::nullopt;
            }
            // p odd: g ≥ 0 iff x ≥ rt. Bracket = {0} ∪ [rt, ∞).
            if (T >= 0) {
                // rt ≥ 0. Union {0} ∪ [rt, ∞) — over-approx [0, ∞).
                return intersect(kZero, xBox.hi);
            }
            // T < 0: rt < 0. Union {0} ∪ [rt, ∞) = [rt, ∞).
            mpq_class rtLo = rootFloor(T);
            return intersect(rtLo, xBox.hi);
        }
        // k odd. x^k · g ≥ 0 iff (x > 0 ∧ g ≥ 0) ∨ (x < 0 ∧ g ≤ 0) ∨ x = 0.
        if (pEven) {
            if (T < 0) {
                // g > 0 always. G+ = (0, ∞), G- = ∅. Bracket [0, ∞).
                return intersect(kZero, xBox.hi);
            }
            // T ≥ 0: G+ = [rt, ∞); G- = [-rt, 0). Bracket [-rt, ∞).
            mpq_class rtCeil = mpqRootCeil(T, p);
            mpq_class negRtCeil(-rtCeil);
            return intersect(negRtCeil, xBox.hi);
        }
        // k odd, p odd: G+ = (0, ∞) ∩ [rt, ∞); G- = (-∞, 0) ∩ (-∞, rt].
        // All three cases (T >0, =0, <0) collapse to no useful narrowing
        // (the union always spans both sides of zero).
        return std::nullopt;
    }

    return std::nullopt;
}

std::optional<IntervalQ> RelationContractorQ::tryNarrowCauchyBracket(
        const std::vector<mpz_class>& coeffs, Relation rel,
        const IntervalQ& xBox) const {
    // Scope: any univariate where V2 (deg-2) / V3a (pure monomial) /
    // V3b (monomial + non-zero constant) and the sparse-pair Eq helper
    // can't help. Need degree ≥ 2 and at least 2 non-zero coefficients
    // (the all-but-leading-zero case is V3a's territory and reaches
    // here only when V3a's rel-specific case-split declines, in which
    // case Cauchy is still sound but rarely informative).
    if (coeffs.size() < 3) return std::nullopt;
    if (coeffs[0] == 0) return std::nullopt;

    int nonZero = 0;
    for (const auto& c : coeffs) {
        if (c != 0) ++nonZero;
    }
    if (nonZero < 2) return std::nullopt;

    // |a_d|, then max_{i < d} |a_i| / |a_d|.
    mpz_class an = coeffs[0];
    if (an < 0) an = -an;

    mpq_class maxRatio(0);
    for (size_t i = 1; i < coeffs.size(); ++i) {
        mpz_class ai = coeffs[i];
        if (ai < 0) ai = -ai;
        mpq_class ratio(ai, an);
        ratio.canonicalize();
        if (ratio > maxRatio) maxRatio = ratio;
    }
    mpq_class M = mpq_class(1) + maxRatio;
    mpq_class negM(-M);  // materialize

    // Normalize a > 0 by flipping rel when negating.
    bool aPositive = (coeffs[0] > 0);
    Relation r = aPositive ? rel : flipSign(rel);

    size_t d = coeffs.size() - 1;
    bool dEven = (d % 2 == 0);

    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    auto intersect = [&](const mpq_class& lo, const mpq_class& hi) -> IntervalQ {
        mpq_class newLo = std::max(xBox.lo, lo);
        mpq_class newHi = std::min(xBox.hi, hi);
        if (newLo > newHi) return kEmpty;
        return IntervalQ{newLo, newHi};
    };

    switch (r) {
        case Relation::Eq:
            // Roots ⊂ [-M, M].
            return intersect(negM, M);
        case Relation::Leq:
        case Relation::Lt:
            if (dEven) {
                // a > 0 even-d: feasible ⊂ root span ⊂ [-M, M].
                return intersect(negM, M);
            } else {
                // a > 0 odd-d: feasible extends to -∞; only upper bound informative.
                return intersect(xBox.lo, M);
            }
        case Relation::Geq:
        case Relation::Gt:
            if (dEven) {
                // a > 0 even-d Geq: feasible is "outside the roots" — a union
                // of two unbounded sets ⇒ skip (not a single interval).
                return std::nullopt;
            } else {
                // a > 0 odd-d Geq: feasible extends to +∞; only lower bound informative.
                return intersect(negM, xBox.hi);
            }
        case Relation::Neq:
        default:
            return std::nullopt;
    }
}

} // namespace xolver
