#include "theory/arith/nra/projection/LazardProjectionOperator.h"
#include "theory/arith/nra/projection/Squarefree.h"
#include "theory/arith/nra/projection/SubresultantChain.h"

namespace nlcolver {

namespace {

// psc_0(f, g) == res_v(f, g) up to sign; for projection only the real zero set
// matters, so the sign is irrelevant. Budget is enforced via the chain's cap.
struct ResOut { RationalPolynomial poly; bool budgetExceeded = false; bool present = false; };

ResOut topResultant(const RationalPolynomial& f, const RationalPolynomial& g,
                    VarId v, int maxMatrixDim) {
    ResOut out;
    auto chain = principalSubresultantCoefficients(f, g, v, maxMatrixDim);
    if (chain.budgetExceeded) { out.budgetExceeded = true; return out; }
    if (chain.psc.empty()) return out;        // degenerate (a side has degree < 1)
    out.poly = chain.psc[0];
    out.poly.normalize();
    out.present = true;
    return out;
}

}  // namespace

LazardOpResult lazardProjectStep(const std::vector<RationalPolynomial>& E, VarId v,
                                 const LazardProjectionConfig& cfg) {
    LazardOpResult r;

    auto emit = [&](RationalPolynomial poly, LazardProjectionOpKind op,
                    const RationalPolynomial* p1, const RationalPolynomial* p2) {
        poly.normalize();
        LazardItem it;
        it.poly = std::move(poly);
        it.op = op;
        if (p1) { it.parent1 = *p1; it.hasParent1 = true; }
        if (p2) { it.parent2 = *p2; it.hasParent2 = true; }
        r.items.push_back(std::move(it));
    };

    std::vector<RationalPolynomial> factors;   // squarefree factors (deg_v >= 1)

    for (const auto& p : E) {
        if (!p.contains(v)) continue;          // already lower-level; nothing to project here

        // Content_v(p): a non-constant content is a lower-level boundary poly.
        auto c = contentWrt(p, v);
        if (!c.complete) {
            r.complete = false;
            r.reason = LazardIncompleteReason::ProjectionKernelFailure;
            return r;
        }
        if (!c.poly.isZero() && !c.poly.isConstant()) emit(c.poly, LazardProjectionOpKind::Content, &p, nullptr);

        // Squarefree primitive part w.r.t. v — the boundary factor.
        auto sf = squarefreePartWrt(p, v);
        if (!sf.complete) {
            r.complete = false;
            r.reason = LazardIncompleteReason::ProjectionKernelFailure;
            return r;
        }
        RationalPolynomial f = sf.poly;
        if (f.degree(v) < 1) continue;         // squarefree part constant in v: no boundary

        emit(f, LazardProjectionOpKind::SquarefreeFactor, &p, nullptr);
        factors.push_back(f);
        const RationalPolynomial& fref = factors.back();

        // Leading / trailing coefficients (in v); they live in lower vars.
        emit(fref.leadingCoefficient(v), LazardProjectionOpKind::LeadingCoefficient, &fref, nullptr);
        auto coeffs = fref.coefficients(v);
        if (!coeffs.empty()) emit(coeffs[0], LazardProjectionOpKind::TrailingCoefficient, &fref, nullptr);

        // Discriminant = res_v(f, f').
        RationalPolynomial fp = fref.derivative(v);
        if (!fp.isZero()) {
            auto disc = topResultant(fref, fp, v, cfg.maxMatrixDim);
            if (disc.budgetExceeded) {
                r.complete = false;
                r.reason = LazardIncompleteReason::ProjectionBudgetExceeded;
                return r;
            }
            if (disc.present) emit(disc.poly, LazardProjectionOpKind::Discriminant, &fref, &fref);
        }
    }

    // Pairwise resultants between distinct squarefree factors.
    for (size_t a = 0; a < factors.size(); ++a) {
        for (size_t b = a + 1; b < factors.size(); ++b) {
            auto res = topResultant(factors[a], factors[b], v, cfg.maxMatrixDim);
            if (res.budgetExceeded) {
                r.complete = false;
                r.reason = LazardIncompleteReason::ProjectionBudgetExceeded;
                return r;
            }
            if (res.present)
                emit(res.poly, LazardProjectionOpKind::Resultant, &factors[a], &factors[b]);
        }
    }

    return r;
}

}  // namespace nlcolver
