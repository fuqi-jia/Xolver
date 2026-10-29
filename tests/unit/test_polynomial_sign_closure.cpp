#include <doctest/doctest.h>
#include "search/refute/PolynomialSignClosure.h"
#include <algorithm>
#include <random>

using namespace xolver;
namespace {
using Polynomial = RationalPolynomial;
Polynomial variable(VarId id) { return Polynomial::fromVar(id, 1, 1); }
Polynomial constant(int value) { return Polynomial::fromConstant(value); }
void constraint(std::vector<SignRefuteConstraint>& constraints, Polynomial polynomial, Relation relation) {
    constraints.push_back({std::move(polynomial), relation, SatLit::positive(static_cast<SatVar>(constraints.size() + 1))});
}
void checkReasons(const std::vector<SignRefuteConstraint>& constraints, const std::vector<SatLit>& reasons) {
    CHECK_FALSE(reasons.empty());
    for (auto reason : reasons)
        CHECK(std::any_of(constraints.begin(), constraints.end(), [&](const auto& c) { return c.reason == reason; }));
}
bool holds(const SignRefuteConstraint& constraint, const std::unordered_map<VarId, mpq_class>& point) {
    const auto value = constraint.poly.evaluateRational(point);
    switch (constraint.rel) {
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Geq: return value >= 0;
        case Relation::Gt: return value > 0;
    }
    return false;
}
}

TEST_CASE("Polynomial sign closure: strict sums force common positive supports nonzero") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints;
    constraint(constraints, x, Relation::Geq);
    constraint(constraints, y, Relation::Geq);
    constraint(constraints, z, Relation::Geq);
    constraint(constraints, x * y + x * z, Relation::Gt);
    constraint(constraints, x, Relation::Eq);
    const auto conflict = refuteByPolynomialSignClosure(constraints);
    REQUIRE(conflict);
    checkReasons(constraints, *conflict);
}

TEST_CASE("Polynomial sign closure: weak sums with a strict negative term force positive support") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints;
    constraint(constraints, x, Relation::Gt);
    constraint(constraints, y, Relation::Geq);
    constraint(constraints, z, Relation::Geq);
    constraint(constraints, y * z - x, Relation::Geq);
    constraint(constraints, z, Relation::Eq);
    REQUIRE(refuteByPolynomialSignClosure(constraints));
}

TEST_CASE("Polynomial sign closure: cancellation uses nonzero guards and the divisor sign") {
    const auto x = variable(0), y = variable(1);
    for (int sign : {-1, 1}) {
        std::vector<SignRefuteConstraint> constraints;
        constraint(constraints, x, sign > 0 ? Relation::Gt : Relation::Lt);
        constraint(constraints, x * (y - constant(1)), Relation::Geq);
        constraint(constraints, y - constant(1), sign > 0 ? Relation::Lt : Relation::Gt);
        const auto conflict = refuteByPolynomialSignClosure(constraints);
        REQUIRE(conflict);
        checkReasons(constraints, *conflict);
    }
    // x=0,y=0 is a valid model: a nonnegative factor may vanish.
    std::vector<SignRefuteConstraint> weak;
    constraint(weak, x, Relation::Geq);
    constraint(weak, x * (y - constant(1)), Relation::Geq);
    constraint(weak, y, Relation::Eq);
    CHECK_FALSE(refuteByPolynomialSignClosure(weak));
}

TEST_CASE("Polynomial sign closure: exact affine identities expose a negative remainder") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints;
    constraint(constraints, x, Relation::Geq);
    constraint(constraints, y - constant(1), Relation::Geq);
    constraint(constraints, z, Relation::Gt);
    constraint(constraints, x - x * y - z, Relation::Geq);
    PolynomialSignStatistics statistics;
    const auto conflict = refuteByPolynomialSignClosure(constraints, &statistics);
    REQUIRE(conflict);
    CHECK(statistics.divisions > 0);
    CHECK_FALSE(statistics.exhausted);
    checkReasons(constraints, *conflict);
}

TEST_CASE("Polynomial sign closure: contradictory rational bounds retain strict endpoints") {
    const auto x = variable(0);
    auto lower = x;
    lower *= mpq_class(3);
    lower.addConstant(mpq_class(-1));
    std::vector<SignRefuteConstraint> constraints;
    constraint(constraints, lower, Relation::Gt);
    constraint(constraints, -lower, Relation::Geq);
    REQUIRE(refuteByPolynomialSignClosure(constraints));
    constraints[0].rel = Relation::Geq;
    CHECK_FALSE(refuteByPolynomialSignClosure(constraints)); // x=1/3
}

TEST_CASE("Polynomial sign closure: a finite support chain avoids nonlinear projection") {
    // A real-valid termination-style contradiction. The strict final sum
    // forces x>0, then b=1, k=1, t=0, u>0, q>0, a>=1, and finally -q*x<0.
    const auto x = variable(0), b = variable(1), k = variable(2);
    const auto t = variable(3), n = variable(4), u = variable(5);
    const auto q = variable(6), a = variable(7), z = variable(8), w = variable(9);
    std::vector<SignRefuteConstraint> constraints;
    for (VarId id = 0; id < 10; ++id) constraint(constraints, variable(id), Relation::Geq);
    constraint(constraints, (b - constant(1)) * x, Relation::Eq);
    constraint(constraints, b * (n - constant(1)), Relation::Geq);
    constraint(constraints, b * n * (constant(1) - k), Relation::Geq);
    constraint(constraints, x * (k - constant(1)), Relation::Geq);
    constraint(constraints, b * (z - z * k - t), Relation::Geq);
    constraint(constraints, b * (q * a - q * k), Relation::Geq);
    constraint(constraints, b * (z - z * k + w * q - u), Relation::Geq);
    constraint(constraints, z - z * a - q * x, Relation::Geq);
    constraint(constraints, u * x + u * t * x - z * t, Relation::Gt);
    PolynomialSignStatistics statistics;
    const auto conflict = refuteByPolynomialSignClosure(constraints, &statistics);
    REQUIRE(conflict);
    CHECK(statistics.cancellations > 0);
    CHECK(statistics.substitutions > 0);
    checkReasons(constraints, *conflict);
}

TEST_CASE("Polynomial sign closure: known rational models survive generated sign constraints") {
    std::mt19937 random(4871);
    for (int instance = 0; instance < 96; ++instance) {
        std::unordered_map<VarId, mpq_class> point;
        for (VarId id = 0; id < 3; ++id)
            point[id] = mpq_class(static_cast<int>(random() % 9) - 4, static_cast<int>(random() % 3) + 1);
        std::vector<SignRefuteConstraint> constraints;
        for (VarId id = 0; id < 3; ++id) {
            constraint(constraints, variable(id), point[id] >= 0 ? Relation::Geq : Relation::Leq);
            if (point[id] != 0 && random() % 2)
                constraint(constraints, variable(id), Relation::Neq);
        }
        for (int row = 0; row < 8; ++row) {
            Polynomial polynomial;
            for (int term = 0; term < 5; ++term) {
                MonomialKey monomial;
                for (VarId id = 0; id < 3; ++id) {
                    const int power = static_cast<int>(random() % 3);
                    if (power) monomial.emplace_back(id, power);
                }
                polynomial.addTerm(monomial, mpq_class(static_cast<int>(random() % 7) - 3));
            }
            polynomial.normalize();
            const auto value = polynomial.evaluateRational(point);
            const auto relation = value == 0 ? Relation::Eq : value > 0 ? Relation::Gt : Relation::Lt;
            constraint(constraints, std::move(polynomial), relation);
        }
        for (const auto& c : constraints) REQUIRE(holds(c, point));
        CHECK_FALSE(refuteByPolynomialSignClosure(constraints));
    }
}
