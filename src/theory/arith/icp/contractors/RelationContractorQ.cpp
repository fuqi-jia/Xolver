#include "theory/arith/icp/contractors/RelationContractorQ.h"
#include "theory/arith/interval/IntervalQOps.h"
#include "theory/arith/interval/IntervalQRoots.h"
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
        // V3 already intersects with xBox internally — change detection is a
        // plain identity check on the bounds.
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
    // V2 scope: only Leq and Lt give a single-interval feasible set when a > 0.
    if (rel != Relation::Leq && rel != Relation::Lt) {
        return std::nullopt;
    }
    if (coeffs.size() != 3) {
        return std::nullopt;
    }

    const mpz_class& a = coeffs[0];
    const mpz_class& b = coeffs[1];
    const mpz_class& c = coeffs[2];

    // With a ≤ 0 the feasible set isn't a single closed interval (a < 0 ⇒
    // parabola opens down, Leq gives a union of unbounded sets; a == 0 means
    // the degree-2 invariant was broken — defensive bail).
    if (a <= 0) {
        return std::nullopt;
    }

    // disc = b² − 4ac (integer arithmetic).
    mpz_class disc = b * b - 4 * a * c;

    if (disc < 0) {
        // No real roots, parabola entirely above 0 ⇒ Leq/Lt impossible.
        // Signal via an empty interval; caller converts to Conflict.
        return IntervalQ{mpq_class(1), mpq_class(0)};
    }

    // Outward sqrt: sqrtDisc ≥ √disc. With 2a > 0 the order is preserved
    // when we divide, so r1Lo ≤ true_r1 and r2Hi ≥ true_r2 — the returned
    // interval is a superset of the true feasible set [r1, r2].
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

} // namespace xolver
