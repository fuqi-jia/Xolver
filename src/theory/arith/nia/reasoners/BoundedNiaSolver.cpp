#include "theory/arith/nia/reasoners/BoundedNiaSolver.h"

namespace nlcolver {

const mpz_class BoundedNiaSolver::ENUMERATION_THRESHOLD = mpz_class(10000);

BoundedNiaSolver::BoundedNiaSolver(PolynomialKernel& kernel) : kernel_(kernel) {}

BoundedSolveResult BoundedNiaSolver::enumerate(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    const IntegerModelValidator& validator,
    const std::vector<std::string>& vars) {

    // Build list of candidate values per variable
    std::vector<std::vector<mpz_class>> values;
    values.reserve(vars.size());

    for (const auto& var : vars) {
        const IntDomain* d = domains.getDomain(var);
        if (!d) {
            return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
        }

        std::vector<mpz_class> varValues;
        if (d->finiteValues && !d->finiteValues->empty()) {
            for (const auto& v : *d->finiteValues) {
                if (d->hasLower && v < d->lower.value) continue;
                if (d->hasUpper && v > d->upper.value) continue;
                if (d->excludedValues.count(v)) continue;
                varValues.push_back(v);
            }
        } else if (d->hasLower && d->hasUpper) {
            for (mpz_class v = d->lower.value; v <= d->upper.value; ++v) {
                if (d->excludedValues.count(v)) continue;
                varValues.push_back(v);
            }
        } else {
            return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
        }

        if (varValues.empty()) {
            // Empty domain for this variable
            return {BoundedSolveStatus::UnsatComplete, std::nullopt,
                    TheoryConflict{std::vector<SatLit>{}}};
        }
        values.push_back(std::move(varValues));
    }

    // Cartesian product enumeration
    std::vector<size_t> indices(vars.size(), 0);

    while (true) {
        // Build current assignment
        IntegerModel model;
        for (size_t i = 0; i < vars.size(); ++i) {
            model[vars[i]] = values[i][indices[i]];
        }

        if (validator.validate(model, constraints)) {
            return {BoundedSolveStatus::Sat, model, std::nullopt};
        }

        // Increment indices
        size_t j = 0;
        while (j < vars.size()) {
            ++indices[j];
            if (indices[j] < values[j].size()) {
                break;
            }
            indices[j] = 0;
            ++j;
        }
        if (j >= vars.size()) {
            // All combinations exhausted
            break;
        }
    }

    // Collect all active reasons for conflict
    std::vector<SatLit> conflictLits;
    for (const auto& c : constraints) {
        conflictLits.push_back(c.reason);
    }

    return {BoundedSolveStatus::UnsatComplete, std::nullopt,
            TheoryConflict{conflictLits}};
}

BoundedSolveResult BoundedNiaSolver::solve(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    const IntegerModelValidator& validator,
    TheoryLemmaDatabase& /*lemmaDb*/) {

    // Collect all variables from constraints
    std::unordered_set<std::string> varSet;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            varSet.insert(v);
        }
    }
    std::vector<std::string> vars(varSet.begin(), varSet.end());

    mpz_class totalSize = domains.totalSize(varSet);
    if (totalSize > ENUMERATION_THRESHOLD) {
        // Phase NIA-Core: interval B&B is a skeleton.
        // For now, return UnknownBudget for large domains.
        return {BoundedSolveStatus::UnknownBudget, std::nullopt, std::nullopt};
    }

    return enumerate(constraints, domains, validator, vars);
}

} // namespace nlcolver
