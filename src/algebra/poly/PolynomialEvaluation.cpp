#include "algebra/poly/PolynomialEvaluation.h"
#include "algebra/poly/PolynomialKernel.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "algebra/poly/LibPolyKernel.h"
#endif
#include <type_traits>

namespace xolver {

std::optional<mpz_class> PolynomialEvaluation::evaluateInteger(PolyId polynomial) const {
    const auto value = evaluate(polynomial);
    if (!value || value->get_den() != 1) return std::nullopt;
    return value->get_num();
}

std::optional<int> PolynomialEvaluation::sign(PolyId polynomial) const {
    const auto value = evaluate(polynomial);
    if (!value) return std::nullopt;
    return mpq_sgn(value->get_mpq_t());
}

namespace {
// Kernel-independent exact fallback. It deliberately uses monomial bindings,
// rather than a variable-support approximation or a default value for absent
// variables. A backend without a polynomial decomposition remains incomplete.
class MonomialEvaluation final : public PolynomialEvaluation {
public:
    template<class Number>
    MonomialEvaluation(const PolynomialKernel& kernel,
        const std::unordered_map<std::string, Number>& model) : kernel_(kernel) {
        for (const auto& [name, value] : model) model_.emplace(name, mpq_class(value));
    }

    std::optional<mpq_class> evaluate(PolyId polynomial) const override {
        const auto terms = kernel_.terms(polynomial);
        if (!terms) return std::nullopt;
        mpq_class sum = 0;
        for (const auto& term : *terms) {
            mpq_class value(term.coefficient);
            for (const auto& [variable, exponent] : term.powers) {
                if (exponent == 0) continue;
                const auto found = model_.find(std::string(kernel_.varName(variable)));
                if (found == model_.end()) return std::nullopt;
                mpq_class power;
                mpz_pow_ui(power.get_num_mpz_t(), found->second.get_num_mpz_t(), exponent);
                mpz_pow_ui(power.get_den_mpz_t(), found->second.get_den_mpz_t(), exponent);
                value *= power;
            }
            sum += value;
        }
        return sum;
    }
private:
    const PolynomialKernel& kernel_;
    std::unordered_map<std::string, mpq_class> model_;
};

#ifdef XOLVER_HAS_LIBPOLY
class LibPolyEvaluation final : public PolynomialEvaluation {
public:
    template<class Number>
    LibPolyEvaluation(const LibPolyKernel& kernel,
        const std::unordered_map<std::string, Number>& model)
        : kernel_(kernel), assignment_(kernel.context()) {
        // Binding the complete candidate once also avoids repeatedly growing
        // and destroying libpoly's dense variable-assignment array for sparse
        // atoms whose variable ids are high in a large model.
        for (const auto& [name, value] : model) {
            if (!kernel_.findVar(name)) continue;
            if constexpr (std::is_same_v<Number, mpz_class>)
                assignment_.set(kernel_.getVariable(name), poly::Value(poly::Integer(value)));
            else
                assignment_.set(kernel_.getVariable(name), poly::Value(poly::Rational(value)));
        }
    }

    std::optional<mpq_class> evaluate(PolyId polynomial) const override {
        const auto& source = kernel_.getPolynomial(polynomial);
        struct BindingCheck { const lp_assignment_t* assignment; bool complete = true; };
        BindingCheck bindings{assignment_.get_internal()};
        lp_polynomial_traverse(source.get_internal(),
            [](const lp_polynomial_context_t*, lp_monomial_t* monomial, void* opaque) {
                auto& check = *static_cast<BindingCheck*>(opaque);
                if (!check.complete) return;
                for (size_t i = 0; i < monomial->n; ++i)
                    if (!lp_assignment_is_set(check.assignment, monomial->p[i].x)) {
                        check.complete = false;
                        return;
                    }
            }, &bindings);
        // libpoly's evaluator requires a complete assignment, and its C++
        // wrapper neither checks that precondition nor owns the returned C
        // value. Check actual monomials and manage the C result explicitly.
        if (!bindings.complete) return std::nullopt;
        const std::unique_ptr<lp_value_t, decltype(&lp_value_delete)> raw(
            lp_polynomial_evaluate(source.get_internal(), assignment_.get_internal()), lp_value_delete);
        if (!raw) return std::nullopt;
        const poly::Value value(raw.get());
        if (poly::is_integer(value))
            return mpq_class(*poly::detail::cast_to_gmp(&poly::as_integer(value)));
        if (poly::is_rational(value))
            return *poly::detail::cast_to_gmp(&poly::as_rational(value));
        return std::nullopt;
    }
private:
    const LibPolyKernel& kernel_;
    poly::Assignment assignment_;
};
#endif

template<class Number>
std::unique_ptr<PolynomialEvaluation> prepare(const PolynomialKernel& kernel,
    const std::unordered_map<std::string, Number>& model) {
#ifdef XOLVER_HAS_LIBPOLY
    if (const auto* libpoly = dynamic_cast<const LibPolyKernel*>(&kernel))
        return std::make_unique<LibPolyEvaluation>(*libpoly, model);
#endif
    return std::make_unique<MonomialEvaluation>(kernel, model);
}
} // namespace

std::unique_ptr<PolynomialEvaluation> makePolynomialEvaluation(const PolynomialKernel& kernel,
    const std::unordered_map<std::string, mpz_class>& model) {
    return prepare(kernel, model);
}

std::unique_ptr<PolynomialEvaluation> makePolynomialEvaluation(const PolynomialKernel& kernel,
    const std::unordered_map<std::string, mpq_class>& model) {
    return prepare(kernel, model);
}

} // namespace xolver
