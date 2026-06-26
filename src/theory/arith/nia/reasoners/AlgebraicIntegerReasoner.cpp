#include "theory/arith/nia/reasoners/AlgebraicIntegerReasoner.h"
#include "util/EnvParam.h"
#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"  // iter-89: completeDivisors
#include <cstdlib>
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include <numeric>

// Helper: GCD for mpz_class using GMP
static mpz_class mpz_gcd(mpz_class a, mpz_class b) {
    mpz_class result;
    mpz_gcd(result.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return result;
}

namespace xolver {

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
    TheoryLemmaStorage& /*lemmaDb*/) {

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

    // iter-84: var-count cap + per-modulus enumeration budget are env-overridable.
    // Sound — UNSAT-only invariant unchanged; relaxing the caps lets the
    // refuter attempt larger systems (potentially closing oracle-UNSAT cases
    // that exceed the iter-79 defaults). Users / autotuner can experiment
    // without recompiling.
    //   XOLVER_NIA_MODULAR_MAX_VARS         (default 15, cap 50)
    //   XOLVER_NIA_MODULAR_MAX_ENUM         (default 50000, cap 1,000,000)
    static const size_t kVarCap = [] {
        long v = env::paramLong("XOLVER_NIA_MODULAR_MAX_VARS", 15);
        if (v > 0 && v <= 50) return static_cast<size_t>(v);
        return size_t(15);
    }();
    static const uint64_t kMaxEnumPerModulus = [] {
        long v = env::paramLong("XOLVER_NIA_MODULAR_MAX_ENUM", 50000);
        if (v > 0 && v <= 1000000) return static_cast<uint64_t>(v);
        return uint64_t(50000);
    }();
    if (allVars.size() > kVarCap) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    std::vector<std::string> vars(allVars.begin(), allVars.end());

    // iter-87: moduli list is env-overridable for autotuner. Default set
    // {2, 3, 4, 5, 7, 8, 9, 11} covers small primes + small 2^k/3^k composites
    // — chosen for catching parity, mod-3 squares-only-{0,1}, and pow-2/3
    // factor contradictions. XOLVER_NIA_MODULAR_MODULI parses a
    // comma-separated list, e.g. "2,3,5,7,11,13" for wider prime coverage.
    // Each modulus is gated by m^N ≤ kMaxEnumPerModulus per the loop below,
    // so adding large moduli (e.g. 13) safely skips at N>4 without changing
    // smaller-N behavior. Soundness invariant unchanged: UNSAT-only.
    static const std::vector<int> moduliVec = [] {
        const char* e = std::getenv("XOLVER_NIA_MODULAR_MODULI");
        if (e && *e) {
            std::vector<int> out;
            const char* p = e;
            while (*p) {
                char* end = nullptr;
                long v = std::strtol(p, &end, 10);
                if (end == p) break;
                if (v >= 2 && v <= 100) out.push_back(static_cast<int>(v));
                p = end;
                if (*p == ',') ++p;
            }
            if (!out.empty()) return out;
        }
        return std::vector<int>{2, 3, 4, 5, 7, 8, 9, 11};
    }();

    // iter-79: generalize from {1,2}-var hardcoded loops to N-var iterative
    // digit-counter enumeration. Sound: same residue-search semantics, just
    // wider variable count. Hard cap on total enumerations per (modulus, varCount)
    // to keep the worst case bounded — 50000 tuples × #constraints per modulus
    // (default; tunable via XOLVER_NIA_MODULAR_MAX_ENUM).
    const size_t N = vars.size();

    for (int m : moduliVec) {
        // Tractability gate: skip this modulus if m^N exceeds the per-modulus cap.
        uint64_t enumSize = 1;
        bool overflow = false;
        for (size_t i = 0; i < N; ++i) {
            if (enumSize > kMaxEnumPerModulus / (uint64_t)m) { overflow = true; break; }
            enumSize *= (uint64_t)m;
        }
        if (overflow) continue;

        bool anySatisfies = false;
        std::vector<int> digits(N, 0);  // current residue tuple

        while (true) {
            // Build model for current digit tuple
            IntegerModel model;
            for (size_t i = 0; i < N; ++i) {
                model[vars[i]] = mpz_class(digits[i]);
            }

            // Check every equality satisfied at this residue assignment
            bool allSatisfied = true;
            for (const auto& c : equalities) {
                auto valOpt = kernel_.evalInteger(c.poly, model);
                if (!valOpt) { allSatisfied = false; break; }
                if (*valOpt % m != 0) { allSatisfied = false; break; }
            }
            if (allSatisfied) { anySatisfies = true; break; }

            // Increment digit counter (LSB-first), m-base
            size_t pos = 0;
            while (pos < N) {
                if (++digits[pos] < m) break;
                digits[pos] = 0;
                ++pos;
            }
            if (pos == N) break;  // overflowed → exhausted all tuples
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

// iter-89: bilinear factor restriction. For an equality `coeff*x*y = -const`
// (single bilinear monomial + constant term), restrict x's and y's domains
// to ±divisors(|const/coeff|). Sound: x*y = c (integer) forces x ∈ divisors(c).
// The set is a sound superset; BoundedNiaSolver checks x*y == c per pair.
//
// Default-OFF via XOLVER_NIA_BILINEAR_FACTOR (matches Step 5 opt-in pattern).
// Divisor enumeration uses UnivariateIntegerReasoner::completeDivisors; only
// fires when the divisor set is fully enumerated (complete=true). Skips when:
//   - |const/coeff| > XOLVER_NIA_BILINEAR_FACTOR_MAX_C (default 10000)
//   - divisor count > XOLVER_NIA_BILINEAR_FACTOR_MAX_DIV (default 64)
//   - division const/coeff is not exact (then it's not a valid integer
//     factoring — falls through silently)
NiaReasoningResult AlgebraicIntegerReasoner::checkBilinearFactor(
    const std::vector<NormalizedNiaConstraint>& equalities,
    DomainStore& domains) {

    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NIA_BILINEAR_FACTOR");
    }();
    if (!enabled) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    static const mpz_class kMaxC = [] {
        long v = env::paramLong("XOLVER_NIA_BILINEAR_FACTOR_MAX_C", 10000);
        if (v > 0 && v <= 1000000) return mpz_class(v);
        return mpz_class(10000);
    }();
    static const size_t kMaxDiv = [] {
        long v = env::paramLong("XOLVER_NIA_BILINEAR_FACTOR_MAX_DIV", 64);
        if (v > 0 && v <= 1000) return static_cast<size_t>(v);
        return size_t(64);
    }();

    bool updated = false;

    for (const auto& c : equalities) {
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        if (termsOpt->size() != 2) continue;  // need exactly one monomial + constant term

        const PolynomialKernel::MonomialTerm* bilinearTerm = nullptr;
        const PolynomialKernel::MonomialTerm* constantTerm = nullptr;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) constantTerm = &t;
            else bilinearTerm = &t;
        }
        if (!bilinearTerm || !constantTerm) continue;

        // iter-91: extended to multilinear — k variables each with exponent 1
        // (k = 2 was the original iter-89 bilinear case). For k >= 3 the same
        // divisor argument applies: if x_i * x_j * ... = c (integers), then
        // each x_i divides c (since the remaining product is integer = c/x_i).
        // Sound: domain restriction to ±divisors(|c|) per variable; the
        // equality filters wrong tuples in BoundedNiaSolver. We cap k <= 4 to
        // keep BoundedNiaSolver's enumeration tractable (the product of per-
        // variable finite domains is divisors^k).
        if (bilinearTerm->powers.size() < 2 || bilinearTerm->powers.size() > 4) continue;
        {
            bool allLinear = true;
            for (const auto& [v, exp] : bilinearTerm->powers) {
                (void)v;
                if (exp != 1) { allLinear = false; break; }
            }
            if (!allLinear) continue;
        }
        if (bilinearTerm->coefficient == 0) continue;

        // Equation: coeff * x * y + const_term = 0  →  x * y = -const_term / coeff
        // Require exact integer division (else this is not a valid factoring).
        mpz_class neg_const = -constantTerm->coefficient;
        if (neg_const % bilinearTerm->coefficient != 0) continue;
        mpz_class c_val = neg_const / bilinearTerm->coefficient;

        // Tractability gates.
        if (abs(c_val) > kMaxC) continue;

        // c_val == 0 is handled by checkFactorDirectConflict (xy=0 with x≠0 ∧ y≠0).
        if (c_val == 0) continue;

        bool complete = true;
        std::set<mpz_class> divs = UnivariateIntegerReasoner::completeDivisors(c_val, complete);
        if (!complete) continue;  // unknown divisor set → can't sound-restrict

        // Build ±divisor set. Soundness: x | c forces x ∈ {±d : d | |c|}.
        std::set<mpz_class> signed_divs;
        for (const auto& d : divs) {
            signed_divs.insert(d);
            signed_divs.insert(-d);
        }
        if (signed_divs.size() > kMaxDiv) continue;

        // iter-91: restrict ALL k variables (was bilinear-only x,y in iter-89).
        // Each var_i | c, so the same signed_divs set bounds every variable
        // in the multilinear monomial. The reason is the single equality.
        for (const auto& [varId, exp] : bilinearTerm->powers) {
            (void)exp;
            std::string vname = std::string(kernel_.varName(varId));
            domains.restrictToFiniteSet(vname, signed_divs, c.reason);
        }
        updated = true;
    }

    if (updated) return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult AlgebraicIntegerReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains,
    TheoryLemmaStorage& lemmaDb) {

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

    // iter-89: bilinear factor restriction — x*y=c → x,y ∈ ±divisors(c).
    // Default-OFF via XOLVER_NIA_BILINEAR_FACTOR; sound domain restriction.
    r = checkBilinearFactor(equalities, domains);
    if (r.kind == NiaReasoningKind::DomainUpdated) updated = true;

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
