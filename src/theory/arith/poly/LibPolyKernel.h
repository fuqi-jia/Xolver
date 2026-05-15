#pragma once

#include "theory/arith/poly/PolynomialKernel.h"

#ifdef NLCOLVER_HAS_LIBPOLY

#include <polyxx.h>
#include <optional>
#include <unordered_map>

namespace nlcolver {

/**
 * LibPolyKernel: wraps libpoly's poly::Polynomial into the NLColver
 * PolynomialKernel interface.
 *
 * Each PolyId indexes a slot in a dense vector of poly::Polynomial.
 * Variables are named strings mapped to poly::Variable objects in a
 * shared poly::Context.
 */
class LibPolyKernel : public PolynomialKernel {
public:
    LibPolyKernel();

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
    std::optional<PolyId> leadingCoefficient(PolyId p) override;
    std::optional<PolyId> substituteRational(PolyId p, VarId v, const mpq_class& value) override;

    // Public accessor for variable id resolution (used by C traverse callback)
    std::optional<VarId> resolveVariableId(lp_variable_t v) const;

    // Accessors for other libpoly-backed components (e.g., CDCAC backend)
    const poly::Context& context() const { return ctx_; }
    const poly::Polynomial& getPolynomial(PolyId id) const { return pool_[id]; }
    poly::Variable getVariable(const std::string& name) const;

private:
    poly::Context ctx_;
    std::vector<poly::Polynomial> pool_;

    // VarId registry: unified variable identity across NLColver
    std::vector<std::string> varNames_;                     // index = VarId
    std::unordered_map<std::string, VarId> nameToVar_;      // name -> VarId
    std::vector<poly::Variable> varIdToPolyVar_;            // VarId -> libpoly variable
    std::unordered_map<lp_variable_t, VarId> polyVarToVarId_; // libpoly var -> VarId

    const poly::Polynomial& get(PolyId id) const { return pool_[id]; }
    poly::Polynomial& get(PolyId id) { return pool_[id]; }
    PolyId alloc(poly::Polynomial p);
    poly::Variable resolvePolyVar(VarId v);
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_LIBPOLY
