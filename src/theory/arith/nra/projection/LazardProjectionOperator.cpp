#include "theory/arith/nra/projection/LazardProjectionOperator.h"
#include "theory/arith/nra/projection/Squarefree.h"
#include "theory/arith/nra/projection/SubresultantChain.h"

#include <cstdlib>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

namespace {

// psc_0(f, g) == res_v(f, g) up to sign; for projection only the real zero set
// matters, so the sign is irrelevant. Budget is enforced via the chain's cap.
struct ResOut { RationalPolynomial poly; bool budgetExceeded = false; bool present = false; };

ResOut topResultant(const RationalPolynomial& f, const RationalPolynomial& g,
                    VarId v, int maxMatrixDim, PolynomialKernel* kernel) {
    ResOut out;
    // forcePsc = (kernel != nullptr): the Lazard operator wants the EXACT
    // libpoly PSC whenever a kernel is available, regardless of the env flag.
    auto chain = principalSubresultantCoefficients(f, g, v, maxMatrixDim, kernel,
                                                   /*forcePsc=*/kernel != nullptr);
    if (chain.budgetExceeded) { out.budgetExceeded = true; return out; }
    if (chain.psc.empty()) return out;        // degenerate (a side has degree < 1)
    out.poly = chain.psc[0];
    out.poly.normalize();
    out.present = true;
    return out;
}

}  // namespace

LazardOpResult lazardProjectStep(const std::vector<RationalPolynomial>& E, VarId v,
                                 const LazardProjectionConfig& cfg,
                                 PolynomialKernel* kernel) {
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
        auto c = contentWrt(p, v, kernel);
        if (!c.complete) {
            r.complete = false;
            r.reason = LazardIncompleteReason::ProjectionKernelFailure;
            return r;
        }
        if (!c.poly.isZero() && !c.poly.isConstant()) emit(c.poly, LazardProjectionOpKind::Content, &p, nullptr);

        // Squarefree primitive part w.r.t. v — the boundary factor.
        auto sf = squarefreePartWrt(p, v, kernel);
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
            auto disc = topResultant(fref, fp, v, cfg.maxMatrixDim, kernel);
            if (disc.budgetExceeded) {
                r.complete = false;
                r.reason = LazardIncompleteReason::ProjectionBudgetExceeded;
                return r;
            }
            if (disc.present) emit(disc.poly, LazardProjectionOpKind::Discriminant, &fref, &fref);
        }
    }

    // Track C round 4.5 / #52: SAFE Lazard shrink — dedup pairwise resultants
    // when input polys produce identical squarefree factors (after normalization).
    // Same factor ⇒ same pairwise resultant ⇒ redundant work. Gated by
    // XOLVER_NRA_CAC_LAZARD_DEDUP; default OFF. Sound because we still emit
    // ALL distinct factors' resultants — only the duplicates are skipped.
    static const bool dedupFactors = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_LAZARD_DEDUP");
        return e && *e && *e != '0';
    }();

    std::vector<size_t> uniqIdx;
    if (dedupFactors && factors.size() > 1) {
        std::unordered_map<std::string, size_t> seen;
        for (size_t i = 0; i < factors.size(); ++i) {
            // Canonical key: unit-normalize then serialize terms. Same key ⇒
            // same factor up to a rational scalar ⇒ identical resultants up to
            // a nonzero rational unit (irrelevant for projection — only real
            // zero sets matter).
            RationalPolynomial p = factors[i];
            p.normalize();
            if (!p.isZero()) {
                const mpq_class lead = p.terms().rbegin()->second;
                if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
            }
            std::string k;
            for (const auto& [mon, coeff] : p.terms()) {
                k += coeff.get_str(); k += ':';
                for (const auto& [vid, e] : mon) { k += std::to_string(vid); k += '^'; k += std::to_string(e); k += ';'; }
                k += '|';
            }
            if (seen.emplace(std::move(k), uniqIdx.size()).second) uniqIdx.push_back(i);
        }
    } else {
        uniqIdx.reserve(factors.size());
        for (size_t i = 0; i < factors.size(); ++i) uniqIdx.push_back(i);
    }

    // Pairwise resultants between distinct squarefree factors (deduped under
    // XOLVER_NRA_CAC_LAZARD_DEDUP).
    for (size_t ia = 0; ia < uniqIdx.size(); ++ia) {
        for (size_t ib = ia + 1; ib < uniqIdx.size(); ++ib) {
            const size_t a = uniqIdx[ia], b = uniqIdx[ib];
            auto res = topResultant(factors[a], factors[b], v, cfg.maxMatrixDim, kernel);
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

}  // namespace xolver
