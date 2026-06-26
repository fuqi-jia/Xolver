#include "theory/arith/logics/nia/reasoners/SumOfSquaresBoundReasoner.h"

namespace xolver {

SumOfSquaresBoundReasoner::SumOfSquaresBoundReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

bool SumOfSquaresBoundReasoner::extractSumOfSquaresForm(
    PolyId poly, std::vector<std::string>& vars, mpz_class& constant) const {

    auto allVars = kernel_.variables(poly);
    if (allVars.empty()) return false;

    // Try to peel off each variable as a pure x^2 term.
    // Start with the original polynomial and subtract each identified square.
    PolyId remaining = poly;
    vars.clear();

    for (const auto& var : allVars) {
        PolyId varPoly = kernel_.mkVar(kernel_.getOrCreateVar(var));
        PolyId varSq = kernel_.pow(varPoly, 2);
        PolyId candidate = kernel_.sub(remaining, varSq);

        // If the candidate no longer contains this variable,
        // then the original had a pure +1 * var^2 term.
        auto candVars = kernel_.variables(candidate);
        bool stillContains = false;
        for (const auto& v : candVars) {
            if (v == var) {
                stillContains = true;
                break;
            }
        }

        if (!stillContains) {
            vars.push_back(var);
            remaining = candidate;
        }
    }

    // After peeling off all pure squares, the remainder must be constant.
    if (!kernel_.isConstant(remaining)) return false;

    mpq_class c = kernel_.toConstant(remaining);
    if (c.get_den() != 1) return false; // non-integer constant
    constant = c.get_num();

    // Must have identified at least one squared term.
    return !vars.empty();
}

NiaReasoningResult SumOfSquaresBoundReasoner::handleConstraint(
    const NormalizedNiaConstraint& c, DomainStore& domains) {

    std::vector<std::string> vars;
    mpz_class constant;
    if (!extractSumOfSquaresForm(c.poly, vars, constant)) {
        return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }

    // poly = Σ xi^2 + constant,  constraint is (Σ xi^2 + constant) rel 0
    // i.e. Σ xi^2 rel (-constant)

    switch (c.rel) {
        case Relation::Leq: {
            // Σ xi^2 + constant <= 0  =>  Σ xi^2 <= -constant
            mpz_class negC = -constant;
            if (negC < 0) {
                // sum of squares <= negative: impossible
                return {NiaReasoningKind::Conflict,
                        TheoryConflict{{c.reason}},
                        std::nullopt};
            }
            // Each |xi| <= floor(sqrt(negC))
            mpz_class bound;
            mpz_sqrt(bound.get_mpz_t(), negC.get_mpz_t());
            for (const auto& var : vars) {
                domains.addLowerBound(var, -bound, c.reason);
                domains.addUpperBound(var, bound, c.reason);
            }
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }

        case Relation::Eq: {
            // Σ xi^2 + constant = 0  =>  Σ xi^2 = -constant
            mpz_class negC = -constant;
            if (negC < 0) {
                return {NiaReasoningKind::Conflict,
                        TheoryConflict{{c.reason}},
                        std::nullopt};
            }
            // Equality implies <=, so same bounds apply
            mpz_class bound;
            mpz_sqrt(bound.get_mpz_t(), negC.get_mpz_t());
            for (const auto& var : vars) {
                domains.addLowerBound(var, -bound, c.reason);
                domains.addUpperBound(var, bound, c.reason);
            }
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }

        case Relation::Geq:
            // Σ xi^2 + constant >= 0  =>  disjunction, deferred
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

        case Relation::Neq:
            // Σ xi^2 + constant != 0: no safe finite bound inference
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

        default:
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }
}

NiaReasoningResult SumOfSquaresBoundReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains) {

    bool updated = false;

    for (const auto& c : constraints) {
        auto r = handleConstraint(c, domains);
        if (r.kind == NiaReasoningKind::Conflict) return r;
        if (r.kind == NiaReasoningKind::DomainUpdated) updated = true;
    }

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
