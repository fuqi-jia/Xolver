#pragma once

#include "theory/arith/poly/PolynomialKernel.h"

#ifdef XOLVER_HAS_LIBPOLY

#include <polyxx.h>
#include <optional>
#include <unordered_map>

namespace xolver {

/**
 * LibPolyKernel: wraps libpoly's poly::Polynomial into the Xolver
 * PolynomialKernel interface.
 *
 * Each PolyId indexes a slot in a dense vector of poly::Polynomial.
 * Variables are named strings mapped to poly::Variable objects in a
 * shared poly::Context.
 */
class LibPolyKernel : public PolynomialKernel {
public:
    LibPolyKernel();
    ~LibPolyKernel() override;   // S1 stats dump on XOLVER_NRA_KERNEL_STATS

    // Variable registry
    VarId getOrCreateVar(std::string_view name) override;
    std::optional<VarId> findVar(std::string_view name) const override;
    std::string_view varName(VarId v) const override;
    bool isValidVar(VarId v) const override;

    PolyId mkZero() override;
    PolyId mkOne() override;
    PolyId mkConst(const mpq_class& c) override;
    PolyId mkVar(VarId v) override;

    PolyId add(PolyId a, PolyId b) override;
    PolyId sub(PolyId a, PolyId b) override;
    PolyId neg(PolyId a) override;
    PolyId mul(PolyId a, PolyId b) override;
    PolyId pow(PolyId a, uint32_t k) override;

    bool isZero(PolyId a) const override;
    bool isConstant(PolyId a) const override;
    mpq_class toConstant(PolyId a) const override;
    std::vector<std::string> variables(PolyId a) const override;
    bool eq(PolyId a, PolyId b) const override;
    int sgn(PolyId a, const std::unordered_map<std::string, mpq_class>& sample) const override;
    int sgnVarId(PolyId a, const std::unordered_map<VarId, mpq_class>& sample) const override;
    std::optional<mpz_class> evalInteger(
        PolyId a,
        const std::unordered_map<std::string, mpz_class>& sample) const override;
    std::optional<mpz_class> evalIntegerVarId(
        PolyId a,
        const std::unordered_map<VarId, mpz_class>& sample) const override;
    std::optional<int> degree(PolyId a, std::string_view var) const override;
    std::optional<std::vector<mpz_class>> getIntegerCoefficients(
        PolyId a, std::string_view var) const override;
    std::optional<std::vector<MonomialTerm>> terms(PolyId a) const override;
    std::string toString(PolyId a) const override;

    std::optional<PolyId> pseudoRemainder(PolyId p, PolyId divisor) override;
    PseudoRemainderResult pseudoRemainderWithScale(PolyId dividend, PolyId divisor, VarId mainVar) override;
    std::optional<PolyId> leadingCoefficient(PolyId p) override;
    std::optional<PolyId> substituteRational(PolyId p, VarId v, const mpq_class& value) override;
    std::optional<PolyId> extractSymbolicResidue(PolyId poly, PolyId modulus) override;

    // Principal subresultant coefficient chain of a, b w.r.t. v, eliminating v
    // (guaranteed via a scoped variable-order push so v is the libpoly main
    // variable). See PolynomialKernel::pscChain for the index convention.
    std::vector<PolyId> pscChain(PolyId a, PolyId b, VarId v) override;

    // Exact multivariate content-aware GCD via lp_polynomial_gcd.
    PolyId gcd(PolyId a, PolyId b) override;

    // Square-free factors via poly::square_free_factors (root-preserving).
    std::vector<PolyId> squareFreeFactors(PolyId a) override;

    // Public accessor for variable id resolution (used by C traverse callback)
    std::optional<VarId> resolveVariableId(lp_variable_t v) const;

    // Accessors for other libpoly-backed components (e.g., CDCAC backend)
    const poly::Context& context() const { return ctx_; }
    const poly::Polynomial& getPolynomial(PolyId id) const { return pool_[id]; }
    poly::Variable getVariable(const std::string& name) const;

    // P2b: expose for LibpolyBackend::projectionPolys
    PolyId alloc(poly::Polynomial p);
    poly::Variable resolvePolyVar(VarId v);

private:
    poly::Context ctx_;
    std::vector<poly::Polynomial> pool_;

    // VarId registry: unified variable identity across Xolver
    std::vector<std::string> varNames_;                     // index = VarId
    std::unordered_map<std::string, VarId> nameToVar_;      // name -> VarId
    std::vector<poly::Variable> varIdToPolyVar_;            // VarId -> libpoly variable
    std::unordered_map<lp_variable_t, VarId> polyVarToVarId_; // libpoly var -> VarId

    // Cache: VarId -> PolyId for single-variable polynomials
    std::unordered_map<VarId, PolyId> varToPoly_;

    // S1 (P6 cas/sqrtmodinv cac-deep) — hash-cons cache for binary ops. Key is
    // (op_tag<<60) | (a<<30) | b (or k for pow, 0 for neg). 30-bit operand
    // slots → up to 2^30 PolyIds per session. NullPoly (uint32 max) is guarded
    // at the call site so its low-30-bit truncation can never collide with a
    // legitimate slot. Add and Mul canonicalize (min, max) before keying since
    // libpoly polynomials commute. Grow-forever: bounded by #unique inputs.
    mutable std::unordered_map<uint64_t, PolyId> binOpCache_;
    mutable uint64_t binOpHits_ = 0;   // S1 stats (XOLVER_NRA_KERNEL_STATS)
    mutable uint64_t binOpMisses_ = 0;
    static constexpr uint64_t binOpKey(uint64_t op, PolyId a, uint32_t b) {
        return (op << 60) | (static_cast<uint64_t>(a) << 30) | static_cast<uint64_t>(b);
    }

    const poly::Polynomial& get(PolyId id) const { return pool_[id]; }
    poly::Polynomial& get(PolyId id) { return pool_[id]; }
};

} // namespace xolver

#endif // XOLVER_HAS_LIBPOLY
