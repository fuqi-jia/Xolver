#include "theory/arith/nia/reasoners/BoundedNiaSolver.h"

#include <unordered_set>

namespace xolver {

const mpz_class BoundedNiaSolver::ENUMERATION_THRESHOLD = mpz_class(10000);
const mpz_class BoundedNiaSolver::PARTIAL_VAR_RANGE_CAP = mpz_class(16);
const mpz_class BoundedNiaSolver::PARTIAL_BUDGET = mpz_class(4096);

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

    bool anyIndeterminate = false;
    while (true) {
        // Build current assignment
        IntegerModel model;
        for (size_t i = 0; i < vars.size(); ++i) {
            model[vars[i]] = values[i][indices[i]];
        }

        auto vres = validator.validate(model, constraints);
        if (vres == IntegerModelValidator::Result::Valid) {
            return {BoundedSolveStatus::Sat, model, std::nullopt};
        }
        if (vres == IntegerModelValidator::Result::Indeterminate) {
            anyIndeterminate = true;
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

    if (anyIndeterminate) {
        return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
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
    TheoryLemmaStorage& /*lemmaDb*/) {

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

BoundedSolveResult BoundedNiaSolver::solvePartial(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains,
        const IntegerModelValidator& validator) {
    // Collect every variable mentioned by any constraint. We want the full
    // VARIABLE SET (bounded ∪ unbounded) so the candidate model can name
    // every variable the validator needs to evaluate the constraints.
    std::unordered_set<std::string> varSet;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) varSet.insert(v);
    }
    if (varSet.empty()) {
        // No vars to assign — IntegerModel{} validates iff all constraints
        // are constant-true. Delegate to the validator.
        IntegerModel empty;
        auto vres = validator.validate(empty, constraints);
        if (vres == IntegerModelValidator::Result::Valid) {
            return {BoundedSolveStatus::Sat, empty, std::nullopt};
        }
        return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
    }

    // Partition into bounded (small finite-range domain) vs unbounded.
    // A var is "bounded" for this purpose iff:
    //   - it has both lower and upper bounds, AND
    //   - upper - lower + 1 <= PARTIAL_VAR_RANGE_CAP, AND
    //   - it isn't restricted to a non-empty finite set (those go through
    //     enumerate() — caller already tried).
    std::vector<std::string> bounded;
    std::vector<std::string> unbounded;
    std::vector<std::vector<mpz_class>> boundedValues;
    mpz_class boundedProduct = 1;
    for (const auto& v : varSet) {
        const IntDomain* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            mpz_class range = d->upper.value - d->lower.value + 1;
            if (range >= 1 && range <= PARTIAL_VAR_RANGE_CAP) {
                std::vector<mpz_class> vals;
                vals.reserve(range.get_ui());
                for (mpz_class x = d->lower.value; x <= d->upper.value; ++x) {
                    if (d->excludedValues.count(x)) continue;
                    vals.push_back(x);
                }
                if (vals.empty()) {
                    // Empty bounded domain — original is UNSAT in the
                    // bounded subset. We don't claim it (the full-domain
                    // enumerate() does that with proper conflict reasons);
                    // bail to Unknown so the caller's pipeline can.
                    return {BoundedSolveStatus::UnknownUnsupported,
                            std::nullopt, std::nullopt};
                }
                boundedProduct *= vals.size();
                if (boundedProduct > PARTIAL_BUDGET) {
                    return {BoundedSolveStatus::UnknownUnsupported,
                            std::nullopt, std::nullopt};
                }
                bounded.push_back(v);
                boundedValues.push_back(std::move(vals));
                continue;
            }
        }
        unbounded.push_back(v);
    }
    if (bounded.empty()) {
        // Nothing to enumerate — the lever doesn't apply.
        return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
    }

    // Candidate-value set for each unbounded variable. Small fixed set
    // covers the typical "trivial" SAT case (all unbounded vars settle at
    // 0 or ±1) plus a couple of within-domain anchors when a partial
    // bound is known. We do NOT include random samples — keeps the
    // enumeration deterministic + bounded.
    auto unboundedGuesses = [&](const std::string& v) -> std::vector<mpz_class> {
        std::vector<mpz_class> g{mpz_class(0), mpz_class(1), mpz_class(-1)};
        const IntDomain* d = domains.getDomain(v);
        if (d) {
            if (d->hasLower) {
                g.push_back(d->lower.value);
                g.push_back(d->lower.value + 1);
            }
            if (d->hasUpper) {
                g.push_back(d->upper.value);
                g.push_back(d->upper.value - 1);
            }
        }
        // Dedupe + filter against any known bounds.
        std::vector<mpz_class> out;
        for (const auto& x : g) {
            if (d) {
                if (d->hasLower && x < d->lower.value) continue;
                if (d->hasUpper && x > d->upper.value) continue;
                if (d->excludedValues.count(x)) continue;
            }
            bool dup = false;
            for (const auto& y : out) if (y == x) { dup = true; break; }
            if (!dup) out.push_back(x);
        }
        if (out.empty()) out.push_back(mpz_class(0));
        return out;
    };

    std::vector<std::vector<mpz_class>> unboundedValues;
    unboundedValues.reserve(unbounded.size());
    mpz_class totalCandidates = boundedProduct;
    for (const auto& v : unbounded) {
        auto g = unboundedGuesses(v);
        totalCandidates *= g.size();
        if (totalCandidates > PARTIAL_BUDGET) {
            return {BoundedSolveStatus::UnknownUnsupported,
                    std::nullopt, std::nullopt};
        }
        unboundedValues.push_back(std::move(g));
    }

    // Cartesian product over (bounded values) × (unbounded guesses). For
    // each candidate model, validate against the ORIGINAL constraints —
    // any Valid result is a sound SAT witness. We never claim UNSAT from
    // this lever because the unbounded vars' full search space is not
    // exhausted.
    const size_t nb = bounded.size();
    const size_t nu = unbounded.size();
    std::vector<size_t> bIdx(nb, 0);
    std::vector<size_t> uIdx(nu, 0);

    while (true) {
        // Build candidate model.
        IntegerModel model;
        for (size_t i = 0; i < nb; ++i) model[bounded[i]] = boundedValues[i][bIdx[i]];
        for (size_t i = 0; i < nu; ++i) model[unbounded[i]] = unboundedValues[i][uIdx[i]];

        auto vres = validator.validate(model, constraints);
        if (vres == IntegerModelValidator::Result::Valid) {
            return {BoundedSolveStatus::Sat, model, std::nullopt};
        }
        // Increment unbounded indices first (inner loop), then bounded
        // (outer). Treats unbounded guesses as the rapidly-cycling dim so
        // each bounded combination tries every unbounded combination.
        size_t j = 0;
        while (j < nu) {
            ++uIdx[j];
            if (uIdx[j] < unboundedValues[j].size()) break;
            uIdx[j] = 0;
            ++j;
        }
        if (j < nu) continue;  // advanced unbounded; retry
        // Advance bounded.
        size_t k = 0;
        while (k < nb) {
            ++bIdx[k];
            if (bIdx[k] < boundedValues[k].size()) break;
            bIdx[k] = 0;
            ++k;
        }
        if (k >= nb) break;  // exhausted everything
        // Reset unbounded indices for next bounded combination.
        for (size_t i = 0; i < nu; ++i) uIdx[i] = 0;
    }

    // No combination validated. NOT a UNSAT verdict — the unbounded
    // vars' search space outside the guess set may still hold a model.
    return {BoundedSolveStatus::UnknownUnsupported, std::nullopt, std::nullopt};
}

} // namespace xolver
