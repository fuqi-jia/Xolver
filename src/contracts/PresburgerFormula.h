#pragma once
#include <gmpxx.h>
#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

namespace xolver::pa {
using Var = uint64_t;
struct Affine {
    std::map<Var, mpz_class> coefficients;
    mpz_class constant = 0;
    mpz_class coefficient(Var v) const {
        auto it = coefficients.find(v);
        return it == coefficients.end() ? mpz_class(0) : it->second;
    }
    void add(const Affine& other, const mpz_class& scale = 1) {
        constant += scale * other.constant;
        for (const auto& [v, c] : other.coefficients) {
            coefficients[v] += scale * c;
            if (coefficients[v] == 0) coefficients.erase(v);
        }
    }
    void multiply(const mpz_class& n) {
        constant *= n;
        if (n == 0) { coefficients.clear(); return; }
        for (auto& [v, c] : coefficients) c *= n;
    }
};
// divisor == 0: affine <= 0. Otherwise: divisor | affine (or its negation).
struct Literal {
    Affine affine;
    mpz_class divisor = 0;
    bool negatedDivisibility = false;
    bool operator<(const Literal& b) const {
        return std::tie(divisor, negatedDivisibility, affine.coefficients, affine.constant) <
               std::tie(b.divisor, b.negatedDivisibility, b.affine.coefficients, b.affine.constant);
    }
};
using Cube = std::vector<Literal>;
using Dnf = std::set<Cube>; // canonical, idempotent disjunction; {} = false; {{}} = true

// Obligations produced by the search algorithm, not trusted proof objects.
// Each step asserts (exists variable. before) iff after over mathematical Int.
struct EliminationStep { Var variable; Dnf before, after; };
struct EliminationTrace {
    std::vector<EliminationStep> steps;
    Dnf closed;
};
// Exact free-variable formula after scoped auxiliaries/binders are eliminated,
// before existential closure. Evidence checking evaluates this representation
// directly; it does not rerun elimination or trust the search's model checks.
struct ModelEvidence {
    Dnf formula;
    std::map<Var, mpz_class> values;
    std::map<std::string, Var> symbols;
    std::set<Var> booleans;
};
} // namespace xolver::pa
