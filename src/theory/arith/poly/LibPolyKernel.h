#pragma once

#include "theory/arith/poly/PolynomialKernel.h"

#ifdef NLCOLVER_HAS_LIBPOLY

#include <polyxx.h>
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

    PolyId mkZero() override;
    PolyId mkOne() override;
    PolyId mkConst(const mpq_class& c) override;
    PolyId mkVar(std::string_view name) override;

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
    std::string toString(PolyId a) const override;

private:
    poly::Context ctx_;
    std::vector<poly::Polynomial> pool_;
    std::unordered_map<std::string, poly::Variable> varMap_;

    const poly::Polynomial& get(PolyId id) const { return pool_[id]; }
    poly::Polynomial& get(PolyId id) { return pool_[id]; }
    PolyId alloc(poly::Polynomial p);
    poly::Variable resolveVar(std::string_view name);
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_LIBPOLY
