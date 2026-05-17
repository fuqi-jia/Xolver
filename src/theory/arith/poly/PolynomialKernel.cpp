#include "theory/arith/poly/PolynomialKernel.h"

#ifdef NLCOLVER_HAS_LIBPOLY
#include "theory/arith/poly/LibPolyKernel.h"
#endif

namespace nlcolver {

#ifdef NLCOLVER_HAS_LIBPOLY

std::unique_ptr<PolynomialKernel> createPolynomialKernel() {
    return std::make_unique<LibPolyKernel>();
}

#else // !NLCOLVER_HAS_LIBPOLY

// Stub implementation: no polynomial support without libpoly.
class StubPolyKernel : public PolynomialKernel {
public:
    PolyId mkZero() override { return 0; }
    PolyId mkOne() override { return 0; }
    PolyId mkConst(const mpq_class& c) override {
        if (c.get_den() != 1) return NullPoly;
        return 0;
    }
    PolyId mkVar(VarId) override { return 0; }
    PolyId add(PolyId, PolyId) override { return 0; }
    PolyId sub(PolyId, PolyId) override { return 0; }
    PolyId neg(PolyId) override { return 0; }
    PolyId mul(PolyId, PolyId) override { return 0; }
    PolyId pow(PolyId, uint32_t) override { return 0; }
    bool isZero(PolyId a) const override { return a == 0; }
    bool isConstant(PolyId a) const override { return a == 0 || a == NullPoly; }
    mpq_class toConstant(PolyId a) const override {
        (void)a;
        return mpq_class(0);
    }
    std::vector<std::string> variables(PolyId) const override { return {}; }
    bool eq(PolyId a, PolyId b) const override { return a == b; }
    int sgn(PolyId a, const std::unordered_map<std::string, mpq_class>&) const override {
        (void)a;
        return 0;
    }
    int sgnVarId(PolyId a, const std::unordered_map<VarId, mpq_class>& sample) const override {
        return PolynomialKernel::sgnVarId(a, sample);
    }
    std::optional<mpz_class> evalInteger(
        PolyId,
        const std::unordered_map<std::string, mpz_class>&) const override {
        return std::nullopt;
    }
    std::optional<mpz_class> evalIntegerVarId(
        PolyId a,
        const std::unordered_map<VarId, mpz_class>& sample) const override {
        return PolynomialKernel::evalIntegerVarId(a, sample);
    }
    std::optional<int> degree(PolyId, std::string_view) const override {
        return std::nullopt;
    }
    std::optional<std::vector<mpz_class>> getIntegerCoefficients(
        PolyId, std::string_view) const override {
        return std::nullopt;
    }
    std::string toString(PolyId) const override { return "stub"; }
};

std::unique_ptr<PolynomialKernel> createPolynomialKernel() {
    return std::make_unique<StubPolyKernel>();
}

#endif

} // namespace nlcolver
