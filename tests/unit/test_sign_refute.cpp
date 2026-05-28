// Positive-orthant sign-definiteness refuter (the Sturm-MBO lever).
// vars sign-fixed by bounds; a same-sign-monomial polynomial is sign-definite
// and refutes a contradicting relation.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/refute/SignDefinitenessRefuter.h"

using namespace xolver;

static const VarId X = VarId{1}, Y = VarId{2};

// A single monomial coeff*∏ v^e as a polynomial.
static RationalPolynomial term(long coeff, std::vector<std::pair<VarId, int>> ve) {
    RationalPolynomial p;
    MonomialKey key;
    for (auto& p2 : ve) key.push_back(p2);
    p.addTerm(key, mpq_class(coeff));
    p.normalize();
    return p;
}
static SatLit lit(unsigned v) { return SatLit::positive(v); }
static SignRefuteConstraint con(RationalPolynomial p, Relation r, unsigned v) {
    return {std::move(p), r, lit(v)};
}
// x>0, y>0 bounds (poly = the var, rel Gt).
static SignRefuteConstraint posBound(VarId v, unsigned reason) {
    return con(term(1, {{v, 1}}), Relation::Gt, reason);
}

TEST_CASE("sign-refute: Sturm-like all-positive equality is UNSAT") {
    // x>0, y>0, x^2*y + x = 0  → g>0 → UNSAT.
    RationalPolynomial g = term(1, {{X, 2}, {Y, 1}}) + term(1, {{X, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {
        posBound(X, 1), posBound(Y, 2), con(g, Relation::Eq, 3)};
    auto r = refuteBySignDefiniteness(cs);
    REQUIRE(r.has_value());
    CHECK(r->size() >= 1);   // conflict carries g's reason + bound reasons
}

TEST_CASE("sign-refute: mixed-sign monomials → no refutation") {
    // x>0, y>0, x - y = 0  → not sign-definite → SAT-possible → no refute.
    RationalPolynomial g = term(1, {{X, 1}}) + term(-1, {{Y, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {
        posBound(X, 1), posBound(Y, 2), con(g, Relation::Eq, 3)};
    CHECK_FALSE(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: all-positive g > 0 is consistent (no refute)") {
    RationalPolynomial g = term(1, {{X, 2}, {Y, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {
        posBound(X, 1), posBound(Y, 2), con(g, Relation::Gt, 3)};
    CHECK_FALSE(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: all-positive g <= 0 is UNSAT") {
    RationalPolynomial g = term(1, {{X, 2}, {Y, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {
        posBound(X, 1), posBound(Y, 2), con(g, Relation::Leq, 3)};
    CHECK(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: no bounds → no refutation") {
    RationalPolynomial g = term(1, {{X, 2}, {Y, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {con(g, Relation::Eq, 3)};
    CHECK_FALSE(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: a sign-unknown variable → no refutation") {
    // only x bounded; y free → x*y indeterminate.
    RationalPolynomial g = term(1, {{X, 1}, {Y, 1}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {posBound(X, 1), con(g, Relation::Eq, 3)};
    CHECK_FALSE(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: negative var with even exponent is positive") {
    // x < 0, x^2 = 0  → x^2 > 0 → UNSAT.
    RationalPolynomial xneg = term(1, {{X, 1}});            // x < 0
    RationalPolynomial g = term(1, {{X, 2}});
    g.normalize();
    std::vector<SignRefuteConstraint> cs = {
        con(xneg, Relation::Lt, 1), con(g, Relation::Eq, 2)};
    CHECK(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: weak nonneg does not over-refute equality") {
    // x >= 0, x = 0  is SAT (x=0) → must NOT refute.
    RationalPolynomial xnn = term(1, {{X, 1}});             // x >= 0
    RationalPolynomial g = term(1, {{X, 1}});               // x = 0
    std::vector<SignRefuteConstraint> cs = {
        con(xnn, Relation::Geq, 1), con(g, Relation::Eq, 2)};
    CHECK_FALSE(refuteBySignDefiniteness(cs).has_value());
}

TEST_CASE("sign-refute: weak nonneg refutes strict negative") {
    // x >= 0, x < 0  → UNSAT.
    RationalPolynomial xnn = term(1, {{X, 1}});
    RationalPolynomial g = term(1, {{X, 1}});
    std::vector<SignRefuteConstraint> cs = {
        con(xnn, Relation::Geq, 1), con(g, Relation::Lt, 2)};
    CHECK(refuteBySignDefiniteness(cs).has_value());
}
