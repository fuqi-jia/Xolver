#include <doctest/doctest.h>
#include "algebra/poly/PolynomialConstraint.h"
#include "search/boolean/Atomizer.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include <array>

using namespace xolver;

namespace {
// Exercise the real SAT backend with clauses only. Theory observation requires
// an external propagator in production; this harness deliberately installs no
// theory callbacks, so a successful contradiction must come from the aliases.
struct ClauseOnlySat : SatSolver {
    std::unique_ptr<SatSolver> backend = createSatSolver();
    SatVar newVar() override { return backend->newVar(); }
    void addClause(const std::vector<SatLit>& clause) override { backend->addClause(clause); }
    SolveResult solve() override { return backend->solve(); }
    SolveResult solve(const std::vector<SatLit>& assumptions) override {
        return backend->solve(assumptions);
    }
    bool value(SatVar variable) const override { return backend->value(variable); }
    void setDeadline(std::chrono::steady_clock::time_point deadline) override {
        backend->setDeadline(deadline);
    }
};

bool compareZero(const mpq_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}

mpq_class evaluate(const RationalPolynomial& polynomial, int x, int y) {
    mpq_class result = 0;
    for (const auto& [monomial, coefficient] : polynomial.terms()) {
        mpq_class term = coefficient;
        for (auto [variable, exponent] : monomial) {
            REQUIRE(variable < 2);
            for (int i = 0; i < exponent; ++i) term *= variable == 0 ? x : y;
        }
        result += term;
    }
    return result;
}
} // namespace

TEST_CASE("polynomial literal canonicalization preserves exact comparison semantics") {
    RationalPolynomial base;
    base.addVar(0, 2, 2);
    base.addVar(1, 1, -3);
    base.addConstant(1);
    const std::array<mpq_class, 4> scales{mpq_class(-7, 3), -1, 1, mpq_class(11, 5)};
    const std::array<Relation, 6> relations{
        Relation::Eq, Relation::Neq, Relation::Lt, Relation::Leq, Relation::Gt, Relation::Geq};
    for (const auto& scale : scales) for (auto relation : relations) {
        auto original = base;
        original *= scale;
        auto normalized = canonicalPolynomialConstraint(original, relation);
        REQUIRE(normalized);
        CHECK(normalized->key.polynomial.terms().front().second == 1);
        for (int x = -2; x <= 2; ++x) for (int y = -2; y <= 2; ++y) {
            CAPTURE(scale);
            CAPTURE(static_cast<int>(relation));
            CAPTURE(x);
            CAPTURE(y);
            const bool originalValue = compareZero(scale * (2 * x * x - 3 * y + 1), relation);
            const bool canonicalValue = compareZero(
                evaluate(normalized->key.polynomial, x, y), normalized->key.relation);
            CHECK(originalValue == (canonicalValue != normalized->negated));
        }
    }
    for (auto relation : relations)
        CHECK_FALSE(canonicalPolynomialConstraint(RationalPolynomial{}, relation));
}

TEST_CASE("polynomial literal canonicalization identifies scaling and complement") {
    auto polynomial = RationalPolynomial::fromVar(0, 2, -2);
    polynomial.addVar(1, 1, 4);
    auto scaled = polynomial;
    scaled *= mpq_class(-7, 3);
    auto a = canonicalPolynomialConstraint(polynomial, Relation::Leq);
    auto equivalent = canonicalPolynomialConstraint(scaled, Relation::Geq);
    auto opposite = canonicalPolynomialConstraint(scaled, Relation::Lt);
    REQUIRE(a);
    REQUIRE(equivalent);
    REQUIRE(opposite);
    CHECK_FALSE(a->key < equivalent->key);
    CHECK_FALSE(equivalent->key < a->key);
    CHECK(a->negated == equivalent->negated);
    CHECK_FALSE(a->key < opposite->key);
    CHECK_FALSE(opposite->key < a->key);
    CHECK(a->negated != opposite->negated);
    scaled.addConstant(1);
    auto distinct = canonicalPolynomialConstraint(scaled, Relation::Geq);
    REQUIRE(distinct);
    CHECK((a->key < distinct->key || distinct->key < a->key));
}

TEST_CASE("polynomial literal aliases resolve complementary atoms in SAT alone") {
    for (Kind relation : {Kind::Eq, Kind::Leq, Kind::Lt}) {
        CAPTURE(static_cast<int>(relation));
        NativeTerms terms;
        terms.registerSort(0, SortKind::Real);
        terms.registerSort(1, SortKind::Bool);
        auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
        auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
        auto square = terms.addShared({Kind::Mul, 0, {x, x}, {}});
        auto difference = terms.addShared({Kind::Sub, 0, {square, y}, {}});
        auto factor = terms.add({Kind::ConstReal, 0, {}, Payload(std::string(relation == Kind::Eq ? "2" : "-2"))});
        auto scaled = terms.addShared({Kind::Mul, 0, {factor, difference}, {}});
        auto zero = terms.add({Kind::ConstReal, 0, {}, Payload(std::string("0"))});
        auto first = terms.addShared({relation, 1, {square, y}, {}});
        auto complement = relation == Kind::Eq ? Kind::Distinct
                        : relation == Kind::Leq ? Kind::Lt : Kind::Leq;
        auto second = terms.addShared({complement, 1, {scaled, zero}, {}});
        auto kernel = createPolynomialKernel();
        auto sat = std::make_unique<ClauseOnlySat>();
        TheoryAtomRegistry registry;
        Atomizer atomizer(*sat);
        registry.setContext(sat.get(), &atomizer);
        atomizer.setRegistry(&registry);
        atomizer.setDefaultTheory(TheoryId::NRA);
        atomizer.setBoolSortId(1);
        atomizer.setPolynomialKernel(kernel.get());
        auto a = atomizer.atomize(first, terms);
        auto b = atomizer.atomize(second, terms);
        // No polynomial decision procedure is installed. Clauses alone must
        // retain both possible signs and refute both contradictory assignments.
        CHECK(sat->solve({a, b.negated()}) == SatSolver::SolveResult::Sat);
        CHECK(sat->solve({a.negated(), b}) == SatSolver::SolveResult::Sat);
        CHECK(sat->solve({a, b}) == SatSolver::SolveResult::Unsat);
        CHECK(sat->solve({a.negated(), b.negated()}) == SatSolver::SolveResult::Unsat);
    }
}
