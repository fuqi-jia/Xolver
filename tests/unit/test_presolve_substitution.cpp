#include <doctest/doctest.h>
#include "search/presolve/Presolve.h"
#include "search/presolve/AffineSubstitution.h"
#include "search/presolve/PolynomialDefSubstitution.h"
#include "search/presolve/PolynomialEqualityCombination.h"
#include "algebra/linear/RationalSystem.h"
#include "search/presolve/UnivariatePolySignAnalyzer.h"
#include <limits>
#include <set>

using namespace xolver;

namespace {
ReasonNode reason(SatVar variable) {
    ReasonNode result;
    result.baseLiterals.push_back(SatLit::positive(variable));
    return result;
}
std::set<SatVar> support(const std::vector<SatLit>& literals) {
    std::set<SatVar> result;
    for (const auto& literal : literals) {
        CHECK(literal.sign);
        result.insert(literal.var);
    }
    return result;
}
}

TEST_CASE("native presolve declines expansion before consuming a defining equality") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto y = RationalPolynomial::fromVar(1, 1, 1);
    const auto z = RationalPolynomial::fromVar(2, 1, 1);
    PresolveState state;
    state.atoms = {{x - y - z, Relation::Eq, reason(1)},
                   {RationalPolynomial::fromVar(0, 300, 1), Relation::Gt, reason(2)}};
    AffineSubstitution affine;
    CHECK_FALSE(affine.run(state));
    CHECK(state.ledger.size() == 0);
    CHECK(state.substMap.empty());
    CHECK(state.atoms[0].live);
    CHECK(state.atoms[1].poly.degree(0) == 300);
    PolynomialDefSubstitution polynomial;
    CHECK_FALSE(polynomial.run(state));
    CHECK(state.atoms[0].live);
    CHECK(state.ledger.size() == 0);
}

TEST_CASE("native presolve separates algebraic roots from rational bounds") {
    for (const mpq_class upper : {mpq_class(7, 5), mpq_class(3, 2)}) {
        auto kernel = createPolynomialKernel();
        const VarId x = kernel->getOrCreateVar("x");
        const auto variable = RationalPolynomial::fromVar(x, 1, 1);
        PresolveState state;
        state.kernel = kernel.get();
        state.atoms = {{variable * variable - RationalPolynomial::fromConstant(2), Relation::Gt, reason(1)},
                       {variable - RationalPolynomial::fromConstant(upper), Relation::Leq, reason(2)},
                       {variable, Relation::Geq, reason(3)}};
        UnivariatePolySignAnalyzer analyzer;
        analyzer.run(state);
        CHECK(state.hasConflict == (upper == mpq_class(7, 5)));
        if (state.hasConflict) CHECK(support(state.conflict.clause) == std::set<SatVar>{1, 2, 3});
    }
}

TEST_CASE("native presolve separates mixed roots using cuts of their own variable") {
    for (const mpq_class upper : {mpq_class(7, 5), mpq_class(3, 2)}) {
        auto kernel = createPolynomialKernel();
        const auto xId = kernel->getOrCreateVar("x");
        const auto yId = kernel->getOrCreateVar("y");
        const auto x = RationalPolynomial::fromVar(xId, 1, 1);
        const auto y = RationalPolynomial::fromVar(yId, 1, 1);
        const auto constant = RationalPolynomial::fromConstant;
        PresolveState state;
        state.kernel = kernel.get();
        // The x polynomial has a rational root and two irrational roots.
        // Bounds for y must not replace x's cuts in the lazily built index.
        state.atoms = {{(x * x - constant(2)) * (x - constant(1)), Relation::Eq, reason(1)},
                       {y * y - constant(3), Relation::Eq, reason(2)},
                       {y - constant(1), Relation::Geq, reason(3)},
                       {y - constant(2), Relation::Leq, reason(4)},
                       {x - constant(1), Relation::Gt, reason(5)},
                       {x - constant(upper), Relation::Leq, reason(6)}};
        UnivariatePolySignAnalyzer analyzer;
        analyzer.run(state);
        CHECK(state.hasConflict == (upper == mpq_class(7, 5)));
        if (state.hasConflict)
            CHECK(support(state.conflict.clause) == std::set<SatVar>{1, 5, 6});
    }
}

TEST_CASE("native presolve retains exact rational-root endpoints in either domain") {
    for (const bool integerDomain : {false, true}) {
        auto kernel = createPolynomialKernel();
        const auto id = kernel->getOrCreateVar("x");
        const auto x = RationalPolynomial::fromVar(id, 1, 1);
        const auto one = RationalPolynomial::fromConstant(1);
        const auto two = RationalPolynomial::fromConstant(2);
        PresolveState state;
        state.kernel = kernel.get();
        state.integerDomain = integerDomain;
        state.atoms = {{(x - one) * (x - two), Relation::Eq, reason(1)},
                       {x - one, Relation::Gt, reason(2)},
                       {x - two, Relation::Lt, reason(3)}};
        UnivariatePolySignAnalyzer analyzer;
        analyzer.run(state);
        REQUIRE(state.hasConflict);
        CHECK(support(state.conflict.clause) == std::set<SatVar>{1, 2, 3});
    }
}

TEST_CASE("native presolve composed substitutions retain every source premise") {
    PresolveState state;
    auto y = RationalPolynomial::fromVar(1, 1, 1);
    REQUIRE(registerSubstitution(state, 0, y + RationalPolynomial::fromConstant(1), reason(1)));
    const size_t first = state.substMap.at(0).factIndex;
    REQUIRE(registerSubstitution(state, 1, RationalPolynomial::fromConstant(2), reason(2)));
    REQUIRE(state.substMap.at(0).value.isConstant());
    CHECK(state.substMap.at(0).value.constantValue() == 3);
    CHECK(state.fixedValues.at(0).value == 3);
    CHECK(support(state.ledger.flattenReasons(state.substMap.at(0).factIndex)) ==
          std::set<SatVar>{1, 2});
    // Earlier evidence is immutable; composition creates a new derived fact.
    REQUIRE(std::holds_alternative<DerivedSubst>(state.ledger.at(first).payload));
    CHECK(std::get<DerivedSubst>(state.ledger.at(first).payload).value.contains(1));
    state.atoms.push_back({RationalPolynomial::fromVar(2, 1, 1) -
                          RationalPolynomial::fromConstant(4), Relation::Eq, reason(4)});
    REQUIRE(registerSubstitution(state, 2, RationalPolynomial::fromVar(0, 1, 1), reason(3)));
    REQUIRE(state.hasConflict);
    CHECK(support(state.conflict.clause) == std::set<SatVar>{1, 2, 3, 4});
}

TEST_CASE("native presolve expired work leaves atoms and derivations intact") {
    PresolveState state;
    state.atoms = {{RationalPolynomial::fromVar(0, 1, 1) -
                    RationalPolynomial::fromConstant(2), Relation::Eq, reason(1)}};
    state.deadline = std::chrono::steady_clock::now() - std::chrono::seconds(1);
    CHECK_FALSE(registerSubstitution(state, 0, RationalPolynomial::fromConstant(2), reason(1)));
    CHECK(state.atoms[0].live);
    CHECK(state.atoms[0].poly.contains(0));
    CHECK(state.ledger.size() == 0);
    CHECK(state.substMap.empty());
    CHECK(state.fixedValues.empty());
}

TEST_CASE("native presolve cancels nonlinear terms without recombining affine premises") {
    for (const bool integerDomain : {false, true}) {
        const auto x = RationalPolynomial::fromVar(0, 1, 1);
        const auto y = RationalPolynomial::fromVar(1, 1, 1);
        const auto z = RationalPolynomial::fromVar(2, 1, 1);
        const auto one = RationalPolynomial::fromConstant(1);
        PresolveState state;
        state.integerDomain = integerDomain;
        state.atoms = {{x * y + z, Relation::Eq, reason(1)},
                       {y - one, Relation::Eq, reason(2)},
                       {x * y + one, Relation::Eq, reason(3)}};
        for (VarId variable = 3; variable < 259; ++variable)
            state.atoms.push_back({RationalPolynomial::fromVar(variable, 1, 1),
                                   Relation::Eq, reason(variable + 10)});
        const auto originalSize = state.atoms.size();
        PolynomialEqualityCombination combination;
        REQUIRE(combination.run(state));
        REQUIRE_FALSE(state.hasConflict);
        REQUIRE(state.atoms.size() == originalSize + 1);
        const auto& consequence = state.atoms.back();
        CHECK(consequence.poly.terms() == (one - z).terms());
        CHECK(consequence.rel == Relation::Eq);
        CHECK(support(consequence.reasons.baseLiterals) == std::set<SatVar>{1, 3});
        CHECK_FALSE(combination.run(state));
    }
}

TEST_CASE("native presolve discards expired elimination and later derives complete conflicts") {
    const auto x = RationalPolynomial::fromVar(0, 1, 1);
    const auto y = RationalPolynomial::fromVar(1, 1, 1);
    PresolveState state;
    state.atoms = {{x * y, Relation::Eq, reason(1)},
                   {x * y - RationalPolynomial::fromConstant(1), Relation::Eq, reason(2)}};
    state.deadline = std::chrono::steady_clock::now() - std::chrono::seconds(1);
    PolynomialEqualityCombination combination;
    CHECK_FALSE(combination.run(state));
    CHECK_FALSE(state.hasConflict);
    CHECK(state.atoms.size() == 2);
    CHECK(state.ledger.size() == 0);
    state.deadline = std::chrono::steady_clock::time_point::max();
    REQUIRE(combination.run(state));
    REQUIRE(state.hasConflict);
    CHECK(support(state.conflict.clause) == std::set<SatVar>{1, 2});
}

TEST_CASE("native sparse polynomial cancellation agrees with independent dense row spaces") {
    const std::vector<MonomialKey> monomials{
        {}, {{0, 1}}, {{1, 1}}, {{2, 1}}, {{0, 1}, {1, 1}}, {{0, 2}}};
    unsigned seed = 9137;
    const auto random = [&]() {
        seed = seed * 1664525u + 1013904223u;
        return static_cast<int>((seed >> 16) % 7) - 3;
    };
    const auto coefficients = [&](const RationalPolynomial& polynomial) {
        std::vector<mpq_class> row;
        for (const auto& monomial : monomials) {
            const auto found = polynomial.terms().find(monomial);
            row.push_back(found == polynomial.terms().end() ? mpq_class(0) : found->second);
        }
        return row;
    };
    const auto rank = [](const std::vector<std::vector<mpq_class>>& matrix, size_t columns) {
        WorkBudget work(0);
        return linear::solve(matrix, std::vector<mpq_class>(matrix.size()), columns, work).rank;
    };
    for (int sample = 0; sample < 80; ++sample) {
        INFO(sample);
        PresolveState state;
        state.integerDomain = sample % 2;
        std::vector<std::vector<mpq_class>> full, high;
        for (int row = 0; row < 3 + sample % 6; ++row) {
            RationalPolynomial polynomial;
            mpq_class constant = 0;
            for (size_t column = 1; column < monomials.size(); ++column) {
                mpq_class coefficient(random(), 1 + sample % 3);
                coefficient.canonicalize();
                polynomial.addTerm(monomials[column], coefficient);
                constant -= coefficient;
            }
            // Every premise has the common model x=y=z=1, so this test also
            // rejects false conflicts in both domains, including rational coefficients.
            polynomial.addConstant(constant);
            polynomial.normalize();
            state.atoms.push_back({polynomial, Relation::Eq, reason(row + 1)});
            full.push_back(coefficients(polynomial));
            high.push_back({full.back()[4], full.back()[5]});
        }
        const size_t originalSize = state.atoms.size();
        PolynomialEqualityCombination combination;
        combination.run(state);
        REQUIRE_FALSE(state.hasConflict);
        std::vector<std::vector<mpq_class>> affine;
        for (const auto& atom : state.atoms)
            if (totalDegree(atom.poly) <= 1) affine.push_back(coefficients(atom.poly));
        CHECK(rank(affine, monomials.size()) ==
              rank(full, monomials.size()) - rank(high, 2));
        for (size_t index = originalSize; index < state.atoms.size(); ++index) {
            const auto& atom = state.atoms[index];
            const auto sources = support(atom.reasons.baseLiterals);
            REQUIRE_FALSE(sources.empty());
            std::vector<std::vector<mpq_class>> transposed(monomials.size());
            for (const auto source : sources) {
                REQUIRE(source >= 1);
                REQUIRE(source <= originalSize);
                for (size_t column = 0; column < monomials.size(); ++column)
                    transposed[column].push_back(full[source - 1][column]);
            }
            WorkBudget work(0);
            // A separate dense solver verifies the exact consequence using
            // only the original premises named by its explanation.
            CHECK(linear::solve(transposed, coefficients(atom.poly), sources.size(), work).consistent);
        }
        CHECK_FALSE(combination.run(state));
    }
}

TEST_CASE("native presolve rejects cyclic and unrepresentable exponent substitutions") {
    PresolveState state;
    REQUIRE(registerSubstitution(state, 0, RationalPolynomial::fromVar(1, 1, 1), reason(1)));
    CHECK_FALSE(registerSubstitution(state, 1, RationalPolynomial::fromVar(0, 1, 1), reason(2)));
    CHECK(state.ledger.size() == 1);
    CHECK(state.substMap.size() == 1);

    state = {};
    state.atoms = {{RationalPolynomial::fromVar(0, 2, 1), Relation::Eq, reason(1)}};
    CHECK_FALSE(registerSubstitution(state, 0,
        RationalPolynomial::fromVar(1, std::numeric_limits<int>::max(), 1), reason(2)));
    CHECK(state.atoms[0].poly.degree(0) == 2);
    CHECK(state.ledger.size() == 0);
    // This power fits the representation. Computing an unused final square
    // would overflow its exponent even though the requested result fits.
    auto power = RationalPolynomial::fromVar(0, 1, 1).pow(std::numeric_limits<int>::max());
    CHECK(power.degree(0) == std::numeric_limits<int>::max());
    CHECK(power.terms().size() == 1);
}
