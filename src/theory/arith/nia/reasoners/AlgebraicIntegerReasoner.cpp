#include "theory/arith/nia/reasoners/AlgebraicIntegerReasoner.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include <numeric>

// Helper: GCD for mpz_class using GMP
static mpz_class mpz_gcd(mpz_class a, mpz_class b) {
    mpz_class result;
    mpz_gcd(result.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return result;
}

namespace nlcolver {

AlgebraicIntegerReasoner::AlgebraicIntegerReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult AlgebraicIntegerReasoner::checkSquareRules(
    const NormalizedNiaConstraint& c, DomainStore& domains) {

    auto vars = kernel_.variables(c.poly);
    if (vars.size() != 1) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    auto degOpt = kernel_.degree(c.poly, vars[0]);
    if (!degOpt || *degOpt != 2) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    auto coeffsOpt = kernel_.getIntegerCoefficients(c.poly, vars[0]);
    if (!coeffsOpt) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    const auto& coeffs = *coeffsOpt;
    if (coeffs.size() != 3) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // coeffs: [a2, a1, a0] for a2*x^2 + a1*x + a0
    if (coeffs[0] == 1 && coeffs[1] == 0) {
        mpz_class a0 = coeffs[2];
        if (c.rel == Relation::Leq) {
            if (a0 == 0) {
                domains.restrictToFiniteSet(vars[0], {mpz_class(0)}, c.reason);
                return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
            } else if (a0 < 0 || a0 > 0) {
                // x^2 + a0 <= 0 where a0 != 0.
                // Since x^2 >= 0, x^2 + a0 >= a0. If a0 > 0, min > 0. If a0 < 0, min = a0 < 0
                // but x^2 + a0 = 0 only when x^2 = -a0. For a0 < 0, check if -a0 is perfect square.
                // However, x^2 + a0 <= 0 means x^2 <= -a0. For a0 > 0, -a0 < 0, impossible.
                // For a0 < 0, this gives finite domain (handled by bounded solver).
                // Phase NIA-Core: for a0 > 0, UNSAT. For a0 < 0, let bounded solver handle.
                if (a0 > 0) {
                    return {NiaReasoningKind::Conflict,
                            TheoryConflict{{c.reason}},
                            std::nullopt};
                }
            }
        }
        if (c.rel == Relation::Geq && a0 >= 0) {
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
        }
    }

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult AlgebraicIntegerReasoner::checkGcdConflict(
    const NormalizedNiaConstraint& c) {

    if (c.rel != Relation::Eq) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    auto vars = kernel_.variables(c.poly);
    if (vars.size() != 1) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    auto coeffsOpt = kernel_.getIntegerCoefficients(c.poly, vars[0]);
    if (!coeffsOpt) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    const auto& coeffs = *coeffsOpt;
    if (coeffs.empty()) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    mpz_class constantTerm = coeffs.back();
    mpz_class g = 0;
    for (size_t i = 0; i + 1 < coeffs.size(); ++i) {
        g = mpz_gcd(g, abs(coeffs[i]));
    }

    if (g != 0 && constantTerm % g != 0) {
        return {NiaReasoningKind::Conflict,
                TheoryConflict{{c.reason}},
                std::nullopt};
    }

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult AlgebraicIntegerReasoner::checkFactorRules(
    const NormalizedNiaConstraint& c,
    TheoryLemmaDatabase& /*lemmaDb*/) {

    (void)c;
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult AlgebraicIntegerReasoner::checkFactorDirectConflict(
    const std::vector<NormalizedNiaConstraint>& constraints) {

    // Step 1: collect all variables that are asserted != 0
    // Map: variable name -> reason lit of the != 0 constraint
    std::unordered_map<std::string, SatLit> nonZeroVarReasons;

    for (const auto& c : constraints) {
        if (c.rel != Relation::Neq) continue;

        auto vars = kernel_.variables(c.poly);
        if (vars.size() != 1) continue;

        // Verify poly is effectively a single variable (or negated variable)
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        if (termsOpt->size() != 1) continue;

        const auto& term = (*termsOpt)[0];
        if (term.powers.size() != 1) continue;
        if (term.powers[0].second != 1) continue;
        // Coefficient can be any non-zero integer; v != 0  <=>  -v != 0
        if (term.coefficient == 0) continue;

        nonZeroVarReasons[vars[0]] = c.reason;
    }

    if (nonZeroVarReasons.empty()) {
        return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }

    // Step 2: find monomial = 0 constraints where all factors are != 0
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;

        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        if (termsOpt->size() != 1) continue;

        const auto& term = (*termsOpt)[0];
        if (term.coefficient == 0) continue;
        if (term.powers.empty()) continue; // constant = 0, not a product of variables

        // Build conflict: not(monomial=0) OR (var1=0) OR (var2=0) OR ...
        // If every var_i has a != 0 constraint, then all literals in the
        // conflict clause are falsified → UNSAT.
        std::vector<SatLit> conflictLits;
        conflictLits.push_back(c.reason); // monomial = 0 (true reason)

        bool allFactorsNonZero = true;
        for (const auto& [varId, exp] : term.powers) {
            if (exp == 0) continue;
            std::string varName = std::string(kernel_.varName(varId));
            auto it = nonZeroVarReasons.find(varName);
            if (it == nonZeroVarReasons.end()) {
                allFactorsNonZero = false;
                break;
            }
            // not(var != 0)  ==  var == 0
            conflictLits.push_back(it->second);
        }

        if (allFactorsNonZero && conflictLits.size() > 1) {
            return {NiaReasoningKind::Conflict,
                    TheoryConflict{std::move(conflictLits)},
                    std::nullopt};
        }
    }

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

bool AlgebraicIntegerReasoner::evaluateMod(
    PolyId /*poly*/,
    const std::vector<std::string>& /*vars*/,
    const std::vector<int>& /*residues*/,
    int /*modulus*/,
    int& /*result*/) const {
    return false;
}

NiaReasoningResult AlgebraicIntegerReasoner::checkModular(
    const std::vector<NormalizedNiaConstraint>& equalities) {

    if (equalities.empty()) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    std::unordered_set<std::string> allVars;
    for (const auto& c : equalities) {
        for (const auto& v : kernel_.variables(c.poly)) {
            allVars.insert(v);
        }
    }

    if (allVars.size() > 6) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    std::vector<std::string> vars(allVars.begin(), allVars.end());
    const int moduli[] = {2, 3, 4, 5, 7, 8, 9, 11};

    for (int m : moduli) {
        bool anySatisfies = false;

        if (vars.size() == 1) {
            for (int r = 0; r < m; ++r) {
                bool allSatisfied = true;
                for (const auto& c : equalities) {
                    IntegerModel model;
                    model[vars[0]] = mpz_class(r);
                    auto valOpt = kernel_.evalInteger(c.poly, model);
                    if (!valOpt) { allSatisfied = false; break; }
                    if (*valOpt % m != 0) { allSatisfied = false; break; }
                }
                if (allSatisfied) {
                    anySatisfies = true;
                    break;
                }
            }
        } else if (vars.size() == 2) {
            for (int r1 = 0; r1 < m; ++r1) {
                for (int r2 = 0; r2 < m; ++r2) {
                    bool allSatisfied = true;
                    for (const auto& c : equalities) {
                        IntegerModel model;
                        model[vars[0]] = mpz_class(r1);
                        model[vars[1]] = mpz_class(r2);
                        auto valOpt = kernel_.evalInteger(c.poly, model);
                        if (!valOpt) { allSatisfied = false; break; }
                        if (*valOpt % m != 0) { allSatisfied = false; break; }
                    }
                    if (allSatisfied) {
                        anySatisfies = true;
                        break;
                    }
                }
                if (anySatisfies) break;
            }
        } else {
            continue;
        }

        if (!anySatisfies) {
            std::vector<SatLit> conflictLits;
            for (const auto& c : equalities) {
                conflictLits.push_back(c.reason);
            }
            return {NiaReasoningKind::Conflict,
                    TheoryConflict{conflictLits},
                    std::nullopt};
        }
    }

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult AlgebraicIntegerReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains,
    TheoryLemmaDatabase& lemmaDb) {

    std::vector<NormalizedNiaConstraint> equalities;
    bool updated = false;

    for (const auto& c : constraints) {
        auto r = checkSquareRules(c, domains);
        if (r.kind == NiaReasoningKind::Conflict) return r;
        if (r.kind == NiaReasoningKind::DomainUpdated) updated = true;

        r = checkGcdConflict(c);
        if (r.kind == NiaReasoningKind::Conflict) return r;

        r = checkFactorRules(c, lemmaDb);
        if (r.kind == NiaReasoningKind::Conflict) return r;
        if (r.kind == NiaReasoningKind::Lemma) return r;

        if (c.rel == Relation::Eq) {
            equalities.push_back(c);
        }
    }

    auto r = checkModular(equalities);
    if (r.kind == NiaReasoningKind::Conflict) return r;

    // Factor direct conflict (e.g. xy=0 ∧ x≠0 ∧ y≠0 → UNSAT)
    r = checkFactorDirectConflict(constraints);
    if (r.kind == NiaReasoningKind::Conflict) return r;

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
