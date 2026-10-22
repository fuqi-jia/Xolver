#include "base/RuntimeConfig.h"
#include "search/nra/lazard/LazardProjectionOperator.h"
#include "search/nra/lazard/Squarefree.h"
#include "search/nra/lazard/SubresultantChain.h"
#include "base/EnvParam.h"   // XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS firewall (projection input)

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
    // Use the exact backend PSC when a kernel is available.
    auto chain = principalSubresultantCoefficients(f, g, v, maxMatrixDim, kernel);
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

    // Heap-corruption / OOM firewall (crash fix). The Lazard projection of a
    // high-degree mod-2^k system (QF_UFNRA sqrtmodinv-hoenicke modInvFull et al.)
    // accumulates polynomial coefficients across projection levels until libpoly's
    // resultant / gcd / coefficient_add either corrupts the heap (glibc SIGABRT)
    // or OOMs (~3.46 GB → SIGSEGV in coefficient_construct_copy) — NEITHER is
    // catchable by the sigsetjmp harness, so the only safe guard is to refuse the
    // runaway BEFORE any libpoly op touches it. Reject a level whose INPUT already
    // carries a coefficient past the same XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS cap the
    // root-isolation firewall uses (the toPrimitiveInteger build guards the
    // within-level case). complete=false → LazardProjectionClosure marks the
    // closure incomplete → CDCAC returns Unknown — a clean caught unknown, never
    // a wrong verdict and never the 44s/3.46 GB blowup.
    {
        // Separate, LOWER cap than the root-isolation firewall: the projection
        // accumulates coefficients MULTIPLICATIVELY across levels and corrupts
        // libpoly's heap well below the 262144-bit isolation cap (modInvFull
        // corrupts in the 16K..256K-bit band). 65536 bits caps the per-level
        // input without touching isolateRealRoots; tune via env if it regresses a
        // legit deep projection (the nra reg gate is the arbiter).
        const long capBits = [] {
            int v = config::read<config::ReadKind::Int>("XOLVER_NRA_LAZARD_MAX_COEFF_BITS", 65536);
            return v > 0 ? static_cast<long>(v) : 65536L;
        }();
        for (const auto& p : E) {
            for (const auto& [key, coeff] : p.terms()) {
                (void)key;
                if (static_cast<long>(mpz_sizeinbase(coeff.get_num().get_mpz_t(), 2)) > capBits ||
                    static_cast<long>(mpz_sizeinbase(coeff.get_den().get_mpz_t(), 2)) > capBits) {
                    r.complete = false;
                    r.reason = LazardIncompleteReason::ProjectionBudgetExceeded;
                    return r;
                }
            }
        }
    }

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

    // Project every distinct pair of squarefree factors.
    // Pairwise resultants between distinct squarefree factors (deduped under
    for (size_t a = 0; a < factors.size(); ++a) {
        for (size_t b = a + 1; b < factors.size(); ++b) {
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
