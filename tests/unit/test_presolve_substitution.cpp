#include <doctest/doctest.h>
#include "search/presolve/Presolve.h"
#include "search/presolve/AffineSubstitution.h"
#include "search/presolve/PolynomialDefSubstitution.h"
#include "search/presolve/PolynomialEqualityCombination.h"
#include "search/presolve/IntegerLinearAlgebra.h"
#include "search/presolve/IntLinearEqualityCoreHNF.h"
#include "algebra/linear/RationalSystem.h"
#include "search/presolve/UnivariatePolySignAnalyzer.h"
#include <algorithm>
#include <limits>
#include <set>
#include <random>

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

IntMatrix multiplyMatrices(const IntMatrix& left, const IntMatrix& right, size_t columns) {
    IntMatrix product(left.size(), std::vector<mpz_class>(columns));
    for (size_t i = 0; i < left.size(); ++i)
        for (size_t k = 0; k < left[i].size(); ++k)
            for (size_t j = 0; j < columns; ++j)
                product[i][j] += left[i][k] * right[k][j];
    return product;
}

mpq_class determinant(const IntMatrix& matrix) {
    RatMatrix work(matrix.size(), std::vector<mpq_class>(matrix.size()));
    for (size_t i = 0; i < matrix.size(); ++i)
        for (size_t j = 0; j < matrix.size(); ++j) work[i][j] = matrix[i][j];
    mpq_class result = 1;
    for (size_t column = 0; column < work.size(); ++column) {
        size_t pivot = column;
        while (pivot < work.size() && work[pivot][column] == 0) ++pivot;
        if (pivot == work.size()) return 0;
        if (pivot != column) { std::swap(work[pivot], work[column]); result = -result; }
        const mpq_class value = work[column][column];
        result *= value;
        for (size_t row = column + 1; row < work.size(); ++row) {
            const mpq_class factor = work[row][column] / value;
            for (size_t j = column; j < work.size(); ++j)
                work[row][j] -= factor * work[column][j];
        }
    }
    return result;
}

void checkNormalForm(const IntMatrix& matrix, const SmithNormalForm& form) {
    const auto columns = matrix.empty() ? 0 : matrix.front().size();
    REQUIRE(form.m == static_cast<int>(matrix.size()));
    REQUIRE(form.n == static_cast<int>(columns));
    REQUIRE(multiplyMatrices(multiplyMatrices(form.U, matrix, columns), form.V, columns) == form.D);
    CHECK(abs(determinant(form.U)) == 1);
    CHECK(abs(determinant(form.V)) == 1);
    int rank = 0;
    mpz_class previous = 0;
    for (size_t i = 0; i < matrix.size(); ++i)
        for (size_t j = 0; j < columns; ++j) {
            if (i != j) CHECK(form.D[i][j] == 0);
            else {
                const auto& value = form.D[i][j];
                CHECK(value >= 0);
                if (value != 0) {
                    CHECK(static_cast<int>(i) == rank);
                    if (previous != 0) CHECK(value % previous == 0);
                    previous = value;
                    ++rank;
                }
            }
        }
    CHECK(form.rank == rank);
}
}

TEST_CASE("integer normal forms: unit pivots avoid repeated full submatrix scans") {
    constexpr size_t dimension = 40;
    IntMatrix matrix(dimension, std::vector<mpz_class>(dimension));
    for (size_t i = 0; i < dimension; ++i) {
        matrix[i][i] = i % 2 ? -1 : 1;
        for (size_t j = i + 1; j < dimension; ++j)
            matrix[i][j] = static_cast<int>((i + 3 * j) % 5) - 2;
    }
    const auto form = smithNormalForm(matrix);
    checkNormalForm(matrix, *form);
    CHECK(form->rank == static_cast<int>(dimension));
    CHECK(form->pivotEntriesExamined <= 4 * dimension);
    const auto cached = smithNormalForm(matrix);
    CHECK(cached == form);
}

TEST_CASE("integer normal forms: signed rectangular and singular systems retain exact invariants") {
    const std::vector<IntMatrix> examples{
        {}, {{}}, {{}, {}}, {{0, 0, 0}, {0, -6, 0}},
        {{6, 4, 0}, {0, 10, 15}}, {{0, -3}, {2, 5}},
        {{2, 4}, {4, 8}}, {{-2, 0, 0}, {0, 3, 0}, {0, 0, 5}},
        {{0, 1, 0}, {1, 0, 0}}, {{9, 0}, {0, 0}, {0, 7}}};
    for (const auto& matrix : examples) checkNormalForm(matrix, *smithNormalForm(matrix));
    std::minstd_rand random(593271);
    for (int sample = 0; sample < 24; ++sample) {
        const size_t rows = 1 + random() % 5, columns = 1 + random() % 5;
        IntMatrix matrix(rows, std::vector<mpz_class>(columns));
        for (auto& row : matrix)
            for (auto& value : row) value = static_cast<int>(random() % 11) - 5;
        checkNormalForm(matrix, *smithNormalForm(matrix));
    }
}

TEST_CASE("integer normal forms: retained transforms survive memo eviction and caller mutation") {
    IntMatrix matrix{{2, 4}, {3, 9}};
    const auto original = matrix;
    const auto retained = smithNormalForm(matrix);
    matrix[0][0] = 17;
    for (int i = 0; i < 90; ++i)
        (void)smithNormalForm(IntMatrix{{100 + i, 0}, {0, 101 + i}});
    checkNormalForm(original, *retained);
    const auto changed = smithNormalForm(matrix);
    checkNormalForm(matrix, *changed);
    CHECK(retained->D != changed->D);
}

TEST_CASE("native integer presolve reports unchanged congruences as a fixed point") {
    PresolveState state;
    state.integerDomain = true;
    state.atoms = {{RationalPolynomial::fromVar(0, 1, 2) +
                    RationalPolynomial::fromVar(1, 1, 4) -
                    RationalPolynomial::fromConstant(6), Relation::Eq, reason(1)}};
    IntLinearEqualityCoreHNF core;
    CHECK(core.run(state));
    REQUIRE(state.congruences.count(0) == 1);
    CHECK(state.congruences.at(0).modulus == 2);
    CHECK(state.congruences.at(0).residue == 1);
    CHECK_FALSE(core.run(state));
    CHECK_FALSE(state.hasConflict);
    CHECK(state.ledger.size() == 0);
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
