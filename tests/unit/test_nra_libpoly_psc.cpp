// White-box: LibPolyKernel::pscChain — libpoly lp_polynomial_psc wrapper.
//
// Task 0 findings (recorded here per the plan):
//
//  * lp_polynomial_psc(lp_polynomial_t** psc, A1, A2) — C API. The CALLER
//    pre-allocates an array of size min(deg A1, deg A2)+1 of *constructed*
//    lp_polynomial_t* (it uses lp_polynomial_swap into each slot), and owns
//    them afterward. libpoly internally swaps A1/A2 so deg(A1)>=deg(A2).
//    We use the polyxx wrapper poly::psc(p,q) -> std::vector<poly::Polynomial>
//    which allocates the array, calls the C API, and adopts each pointer into
//    an owning poly::Polynomial (deleter attached) — no leak / double-free.
//    Output size = min(deg p, deg q)+1; psc[j] = the j-th principal
//    subresultant coefficient (psc_0 = resultant, psc_n = lc of the lower one).
//    psc computes w.r.t. the polynomials' libpoly MAIN (top) variable.
//
//  * Index alignment: the determinant reference
//    (principalSubresultantCoefficients) returns exactly min(deg) entries,
//    out.psc[j] = psc_j for j=0..min-1. libpoly returns min+1 entries; the
//    extra trailing entry psc[min] (=lc) is dropped so the chains are
//    index-for-index aligned.
//
//  * Main-variable mechanism: libpoly's default variable order leaves all
//    variables "unpushed" (index -1), tie-broken by lp_variable_t id (creation
//    order) — so main_variable is whichever was created last, NOT necessarily
//    the variable we intend to eliminate. LibpolyBackend::projectionPolys only
//    *checks* main_variable==elimVar and bails with UnsupportedVarOrder.
//    pscChain instead GUARANTEES elimination of v by temporarily pushing the
//    context variable order so v is on top (main), computing, then restoring
//    the previous order. This is the cvc5 lp_variable_order_push mechanism.
//
//  * PolyId <-> RationalPolynomial: RationalPolynomial::fromPolyId(id, kernel)
//    (lp->RP) and ::toPrimitiveInteger(kernel) (RP->integer PolyId). pscChain
//    takes/returns PolyId (already lp-backed); the underlying lp_polynomial_t*
//    is LibPolyKernel::getPolynomial(id).get_internal().

#include <doctest/doctest.h>
#include <gmpxx.h>

#include <array>
#include <cstdlib>
#include <random>
#include <sstream>

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/projection/SubresultantChain.h"

// NB: this test never includes LibPolyKernel.h directly — the libpoly include
// path is PRIVATE to xolver_core. pscChain is exposed on the PolynomialKernel
// base interface (default {}), so we drive it through createPolynomialKernel().

using namespace xolver;

#ifdef XOLVER_HAS_LIBPOLY

namespace {

// Canonicalize a RationalPolynomial to a representative of its "up to a nonzero
// rational scale" class: normalize, clear denominators / divide by content
// (toPrimitiveInteger), then fix the sign so the lexicographically-leading
// term's coefficient is positive. Two polynomials equal up to a nonzero
// rational constant produce identical canonical forms.
RationalPolynomial canonicalScale(RationalPolynomial p, PolynomialKernel& kernel) {
    p.normalize();
    if (p.isZero()) return p;  // zero is its own class
    auto norm = p.toPrimitiveInteger(kernel);
    REQUIRE(norm.ok());
    auto rpOpt = RationalPolynomial::fromPolyId(norm.poly, kernel);
    REQUIRE(rpOpt.has_value());
    RationalPolynomial r = *rpOpt;
    r.normalize();
    if (r.isZero()) return r;
    // Fix sign by the leading (last in the sorted map = lex-largest key) term.
    const auto& terms = r.terms();
    const mpq_class& leadCoeff = terms.rbegin()->second;
    if (leadCoeff < 0) {
        r *= mpq_class(-1);
        r.normalize();
    }
    return r;
}

bool equalUpToRationalScale(const RationalPolynomial& a,
                            const RationalPolynomial& b,
                            PolynomialKernel& kernel) {
    RationalPolynomial ca = canonicalScale(a, kernel);
    RationalPolynomial cb = canonicalScale(b, kernel);
    // Both zero?
    if (ca.isZero() && cb.isZero()) return true;
    if (ca.isZero() != cb.isZero()) return false;
    return ca.terms() == cb.terms();
}

// Build a PolyId for a RationalPolynomial in the given kernel (integer-primitive
// up to a positive scale; benign for psc / CAD).
PolyId rpToPolyId(const RationalPolynomial& rp, PolynomialKernel& kernel) {
    RationalPolynomial r = rp;
    r.normalize();
    auto norm = r.toPrimitiveInteger(kernel);
    REQUIRE(norm.ok());
    return norm.poly;
}

// Convenience: VarId for a fresh named variable in the kernel.
VarId mkVarId(PolynomialKernel& k, const char* name) {
    return k.getOrCreateVar(name);
}

}  // namespace

TEST_CASE("pscChain: a = x^2 - s, b = 2x w.r.t. x (chain length 1, = resultant)") {
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId s = mkVarId(kernel, "s");
    VarId x = mkVarId(kernel, "x");

    // a = x^2 - s
    RationalPolynomial aRp;
    aRp.addVar(x, 2, 1);
    aRp.addVar(s, 1, -1);
    aRp.normalize();
    // b = 2x
    RationalPolynomial bRp;
    bRp.addVar(x, 1, 2);
    bRp.normalize();

    PolyId a = rpToPolyId(aRp, kernel);
    PolyId b = rpToPolyId(bRp, kernel);

    std::vector<PolyId> chain = kernel.pscChain(a, b, x);

    // min(deg_x a, deg_x b) = min(2,1) = 1 entry.
    REQUIRE(chain.size() == 1);

    // Reference: the determinant psc chain.
    auto ref = principalSubresultantCoefficients(aRp, bRp, x);
    REQUIRE(ref.psc.size() == 1);
    REQUIRE_FALSE(ref.budgetExceeded);

    auto libRpOpt = RationalPolynomial::fromPolyId(chain[0], kernel);
    REQUIRE(libRpOpt.has_value());
    CHECK(equalUpToRationalScale(*libRpOpt, ref.psc[0], kernel));

    // Hand check: psc_0 of (x^2 - s, 2x) is a nonzero multiple of s (it is the
    // resultant; the discriminant of x^2 - s is proportional to s).
    RationalPolynomial canon = canonicalScale(*libRpOpt, kernel);
    CHECK(canon.degree(s) == 1);
    CHECK_FALSE(canon.contains(x));
}

TEST_CASE("pscChain: matches determinant up to rational scale (two cubics in x)") {
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId y = mkVarId(kernel, "y");
    VarId x = mkVarId(kernel, "x");

    // f = x^3 + 2x + (y - 1),  g = 2x^3 + x^2 + (5)
    RationalPolynomial f;
    f.addVar(x, 3, 1);
    f.addVar(x, 1, 2);
    f.addVar(y, 1, 1);
    f.addConstant(-1);
    f.normalize();
    RationalPolynomial g;
    g.addVar(x, 3, 2);
    g.addVar(x, 2, 1);
    g.addConstant(5);
    g.normalize();

    PolyId fp = rpToPolyId(f, kernel);
    PolyId gp = rpToPolyId(g, kernel);

    std::vector<PolyId> chain = kernel.pscChain(fp, gp, x);
    auto ref = principalSubresultantCoefficients(f, g, x);
    REQUIRE_FALSE(ref.budgetExceeded);

    REQUIRE(chain.size() == ref.psc.size());  // both min(3,3) = 3
    REQUIRE(chain.size() == 3);

    for (size_t j = 0; j < chain.size(); ++j) {
        auto libRpOpt = RationalPolynomial::fromPolyId(chain[j], kernel);
        REQUIRE(libRpOpt.has_value());
        CHECK_MESSAGE(equalUpToRationalScale(*libRpOpt, ref.psc[j], kernel),
                      "psc index " << j << " differs from determinant");
    }
}

TEST_CASE("pscChain: eliminates a NON-top variable correctly (main-variable guarantee)") {
    // Create x AFTER y, so libpoly's default main variable is x, not y.
    // We then eliminate y. pscChain must reorder so y is the main variable,
    // producing a chain in x (and any other vars) — NOT in y.
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId y = mkVarId(kernel, "y");
    VarId x = mkVarId(kernel, "x");  // x is the default top variable

    // f = y^2 - x,  f' (w.r.t y) = 2y. psc_0 = discriminant-like = multiple of x.
    RationalPolynomial f;
    f.addVar(y, 2, 1);
    f.addVar(x, 1, -1);
    f.normalize();
    RationalPolynomial fp = f.derivative(y);  // 2y
    fp.normalize();

    PolyId fId = rpToPolyId(f, kernel);
    PolyId fpId = rpToPolyId(fp, kernel);

    std::vector<PolyId> chain = kernel.pscChain(fId, fpId, y);
    auto ref = principalSubresultantCoefficients(f, fp, y);
    REQUIRE_FALSE(ref.budgetExceeded);
    REQUIRE(chain.size() == ref.psc.size());
    REQUIRE(chain.size() == 1);

    auto libRpOpt = RationalPolynomial::fromPolyId(chain[0], kernel);
    REQUIRE(libRpOpt.has_value());
    CHECK(equalUpToRationalScale(*libRpOpt, ref.psc[0], kernel));

    // The eliminated variable y must NOT appear; only x should remain.
    RationalPolynomial canon = canonicalScale(*libRpOpt, kernel);
    CHECK_FALSE(canon.contains(y));
    CHECK(canon.degree(x) == 1);
}

TEST_CASE("pscChain: degenerate (deg_v < 1 on a side) returns empty chain") {
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId s = mkVarId(kernel, "s");
    VarId x = mkVarId(kernel, "x");

    // a = x^2 (deg_x 2),  c = 5 + s (deg_x 0 -> < 1) => empty chain.
    RationalPolynomial aRp;
    aRp.addVar(x, 2, 1);
    aRp.normalize();
    RationalPolynomial cRp;
    cRp.addVar(s, 1, 1);
    cRp.addConstant(5);
    cRp.normalize();

    PolyId a = rpToPolyId(aRp, kernel);
    PolyId c = rpToPolyId(cRp, kernel);

    std::vector<PolyId> chain = kernel.pscChain(a, c, x);
    CHECK(chain.empty());

    // Symmetric: also empty when the first side has deg_v < 1.
    std::vector<PolyId> chain2 = kernel.pscChain(c, a, x);
    CHECK(chain2.empty());
}

// ---------------------------------------------------------------------------
// Task 2: Randomized differential CAD-equivalence oracle.
//
// The soundness keystone. For ~300 random RationalPolynomial pairs (p,q) over a
// small integer-coefficient grid with modest degrees, and for each variable v
// shared by both with deg_v >= 1 on both sides, we compare:
//   det = principalSubresultantCoefficients(p,q,v,maxMatrixDim)   [reference,
//                                                                  O(n!) determinant]
//   lib = kernel.pscChain(pId, qId, v)                            [libpoly path]
// and assert det.psc.size()==lib.size() and each index equal up to a nonzero
// rational scale. A mismatch means the libpoly path is NOT CAD-equivalent
// (main-variable / index-alignment / normalization bug) — a STOP-and-report
// finding, never weaken the assertion to pass.
// ---------------------------------------------------------------------------
namespace {

// Human-readable rendering of a RationalPolynomial for failure diagnostics.
std::string showRp(const RationalPolynomial& rp,
                   const std::array<VarId, 3>& vars,
                   const std::array<const char*, 3>& names) {
    if (rp.isZero()) return "0";
    std::ostringstream os;
    bool first = true;
    for (const auto& [key, coeff] : rp.terms()) {
        if (!first) os << " + ";
        first = false;
        os << coeff.get_str();
        for (const auto& [vid, exp] : key) {
            const char* nm = "?";
            for (size_t i = 0; i < vars.size(); ++i)
                if (vars[i] == vid) nm = names[i];
            os << "*" << nm << "^" << exp;
        }
    }
    return os.str();
}

}  // namespace

TEST_CASE("pscChain: randomized differential CAD-equivalence vs determinant (~300 pairs)") {
    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;

    // Three candidate variables. Creation order fixes libpoly's default main
    // variable (z, created last) — exercising pscChain's main-variable
    // reordering when we eliminate x or y.
    VarId x = mkVarId(kernel, "x");
    VarId y = mkVarId(kernel, "y");
    VarId z = mkVarId(kernel, "z");
    std::array<VarId, 3> vars{x, y, z};
    std::array<const char*, 3> names{"x", "y", "z"};

    // Deterministic, reproducible RNG (fixed seed).
    std::mt19937 rng(12345);
    std::uniform_int_distribution<int> coeffDist(-3, 3);     // small integer coeffs
    std::uniform_int_distribution<int> nVarsDist(2, 3);      // 2 or 3 variables active
    std::uniform_int_distribution<int> nMonomialsDist(2, 5); // a handful of monomials
    std::uniform_int_distribution<int> degDist(0, 3);        // per-variable degree 0..3

    // Build one random RationalPolynomial over the first `nv` variables.
    auto randomPoly = [&](int nv) {
        RationalPolynomial p;
        int nMon = nMonomialsDist(rng);
        for (int m = 0; m < nMon; ++m) {
            int c = coeffDist(rng);
            if (c == 0) c = 1;  // avoid all-zero monomials
            MonomialKey key;
            for (int vi = 0; vi < nv; ++vi) {
                int e = degDist(rng);
                if (e > 0) key.emplace_back(vars[vi], e);
            }
            // MonomialKey must be sorted by varId; vars[] is already in creation
            // order, but emplace order matches that, so it's already sorted.
            p.addTerm(key, mpq_class(c));
        }
        p.normalize();
        return p;
    };

    const int kNumPairs = 300;
    const int kMaxMatrixDim = 12;

    int pairsTested = 0;
    int comparisons = 0;       // (pair, var) combinations actually compared
    int skippedBudget = 0;     // skipped because determinant bailed
    int mismatches = 0;

    for (int iter = 0; iter < kNumPairs; ++iter) {
        int nv = nVarsDist(rng);
        RationalPolynomial p = randomPoly(nv);
        RationalPolynomial q = randomPoly(nv);
        ++pairsTested;

        for (size_t vi = 0; vi < vars.size(); ++vi) {
            VarId v = vars[vi];
            int dp = p.degree(v);
            int dq = q.degree(v);
            // Both sides must have degree >= 1 in v for a nondegenerate chain.
            if (dp < 1 || dq < 1) continue;

            auto det = principalSubresultantCoefficients(p, q, v, kMaxMatrixDim);
            if (det.budgetExceeded) {
                ++skippedBudget;
                continue;  // no reference to compare against
            }

            PolyId pId = rpToPolyId(p, kernel);
            PolyId qId = rpToPolyId(q, kernel);
            std::vector<PolyId> lib = kernel.pscChain(pId, qId, v);

            ++comparisons;

            // (a) chain length must match.
            if (lib.size() != det.psc.size()) {
                ++mismatches;
                CHECK_MESSAGE(lib.size() == det.psc.size(),
                              "CHAIN LENGTH MISMATCH iter=" << iter
                              << " var=" << names[vi]
                              << " p=[" << showRp(p, vars, names) << "]"
                              << " q=[" << showRp(q, vars, names) << "]"
                              << " lib.size=" << lib.size()
                              << " det.size=" << det.psc.size());
                continue;
            }

            // (b) each index equal up to a nonzero rational scale.
            for (size_t j = 0; j < lib.size(); ++j) {
                auto libRpOpt = RationalPolynomial::fromPolyId(lib[j], kernel);
                REQUIRE(libRpOpt.has_value());
                bool eq = equalUpToRationalScale(*libRpOpt, det.psc[j], kernel);
                if (!eq) {
                    ++mismatches;
                    CHECK_MESSAGE(eq,
                                  "PSC MISMATCH iter=" << iter
                                  << " var=" << names[vi]
                                  << " index=" << j
                                  << " p=[" << showRp(p, vars, names) << "]"
                                  << " q=[" << showRp(q, vars, names) << "]"
                                  << " lib[" << j << "]=[" << showRp(*libRpOpt, vars, names) << "]"
                                  << " det[" << j << "]=[" << showRp(det.psc[j], vars, names) << "]");
                }
            }
        }
    }

    MESSAGE("differential: pairs=" << pairsTested
            << " (pair,var) comparisons=" << comparisons
            << " skipped(budgetExceeded)=" << skippedBudget
            << " mismatches=" << mismatches);

    // Must actually have exercised the path on a meaningful number of cases.
    REQUIRE(comparisons > 50);
    CHECK(mismatches == 0);
}

// ---------------------------------------------------------------------------
// Task 3: the gated public entry point principalSubresultantCoefficients.
//
// The flag XOLVER_NRA_LIBPOLY_PSC selects the libpoly path ONLY when a non-null
// kernel is also supplied (`kernel != nullptr && flag ON`). The flag is read
// once per process via a function-local `static const bool`, so we set the env
// var ON for the whole process and exploit the kernel-null short-circuit to get
// both paths in a single run:
//   * kernel = &kernel  + flag ON  -> libpoly psc path
//   * kernel = nullptr             -> determinant path (the flag is never even
//                                      consulted; this is the byte-identical
//                                      OFF reference)
// The two out.psc chains must be equal up to a nonzero rational scale per entry.
// Any non-equivalence is a STOP-and-report soundness finding.
// ---------------------------------------------------------------------------
TEST_CASE("principalSubresultantCoefficients: gated ON (libpoly) == OFF (determinant) up to scale") {
    // Set the flag ON before the first call so the process-static read sees it.
    setenv("XOLVER_NRA_LIBPOLY_PSC", "1", /*overwrite=*/1);

    auto kernelPtr = createPolynomialKernel();
    PolynomialKernel& kernel = *kernelPtr;
    VarId y = mkVarId(kernel, "y");
    VarId x = mkVarId(kernel, "x");

    // Integer-coefficient polynomials only (libpoly is an integer ring;
    // mkConst(mpq_class(1,2)) returns a NULL poly and crashes).
    // f = x^3 + 2x + (y - 1),  g = 2x^3 + x^2 + 5
    RationalPolynomial f;
    f.addVar(x, 3, 1);
    f.addVar(x, 1, 2);
    f.addVar(y, 1, 1);
    f.addConstant(-1);
    f.normalize();
    RationalPolynomial g;
    g.addVar(x, 3, 2);
    g.addVar(x, 2, 1);
    g.addConstant(5);
    g.normalize();

    // OFF reference: kernel == nullptr forces the determinant path regardless
    // of the env flag (the flag is gated behind the non-null kernel check).
    auto off = principalSubresultantCoefficients(f, g, x, /*maxMatrixDim=*/12, nullptr);
    // ON: non-null kernel + flag ON -> libpoly psc path.
    auto on  = principalSubresultantCoefficients(f, g, x, /*maxMatrixDim=*/12, &kernel);

    REQUIRE_FALSE(off.budgetExceeded);
    REQUIRE_FALSE(on.budgetExceeded);          // libpoly path never bails on budget
    REQUIRE(on.psc.size() == off.psc.size());  // both min(3,3) = 3

    for (size_t j = 0; j < off.psc.size(); ++j) {
        CHECK_MESSAGE(equalUpToRationalScale(on.psc[j], off.psc[j], kernel),
                      "gated psc index " << j
                      << ": libpoly path differs from determinant");
    }

    unsetenv("XOLVER_NRA_LIBPOLY_PSC");
}

#endif  // XOLVER_HAS_LIBPOLY
