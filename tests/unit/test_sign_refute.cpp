// Positive-orthant sign-definiteness refuter (the Sturm-MBO lever).
// vars sign-fixed by bounds; a same-sign-monomial polynomial is sign-definite
// and refutes a contradicting relation.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include <algorithm>
#include "search/refute/SignDefinitenessRefuter.h"

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

TEST_CASE("quadratic-sign: semidefinite coefficient guards refute strict negatives") {
    const VarId a=3, b=4, c=5;
    auto av=term(1,{{a,1}}), bv=term(1,{{b,1}}), cv=term(1,{{c,1}});
    auto determinant=av*cv;determinant*=4;determinant-=bv*bv;
    auto p=av*term(1,{{X,2}})+bv*term(1,{{X,1}})+cv;
    std::vector<SignRefuteConstraint> constraints={con(av,Relation::Geq,10),
        con(cv,Relation::Geq,20),con(determinant,Relation::Geq,30),con(p,Relation::Lt,40)};
    QuadraticSignStatistics stats;
    const auto proof=refuteByQuadraticSigns(constraints,&stats);
    REQUIRE(proof.has_value());
    for(unsigned id:{10U,20U,30U,40U})
        CHECK(std::any_of(proof->begin(),proof->end(),[&](SatLit reason){return reason.var==id;}));
    CHECK(stats.certified==1);
    CHECK_FALSE(stats.exhausted);
}

TEST_CASE("quadratic-sign: a zero leading coefficient still requires a nonnegative constant") {
    const VarId a=3, b=4;
    auto av=term(1,{{a,1}}),bv=term(1,{{b,1}});
    auto p=av*term(1,{{X,2}})+bv*term(1,{{X,1}});p.addConstant(-1);p.normalize();
    auto determinant=av;determinant*=-4;determinant-=bv*bv;
    std::vector<SignRefuteConstraint> constraints={con(av,Relation::Eq,10),
        con(bv,Relation::Eq,20),con(determinant,Relation::Geq,30),con(p,Relation::Lt,40)};
    CHECK_FALSE(refuteByQuadraticSigns(constraints).has_value()); // a=b=0, p=-1 is SAT
}

TEST_CASE("quadratic-sign: touching a zero does not refute equality or a weak bound") {
    auto p=term(1,{{X,2}})+term(2,{{X,1}})+term(1,{}); // (x+1)^2
    CHECK_FALSE(refuteByQuadraticSigns({con(p,Relation::Leq,10)}).has_value());
    CHECK_FALSE(refuteByQuadraticSigns({con(p,Relation::Eq,10)}).has_value());
    CHECK(refuteByQuadraticSigns({con(p,Relation::Lt,10)}).has_value());
    p.addConstant(1);p.normalize();
    CHECK(refuteByQuadraticSigns({con(p,Relation::Leq,10)}).has_value());
    CHECK(refuteByQuadraticSigns({con(p,Relation::Eq,10)}).has_value());
}

TEST_CASE("quadratic-sign: nonlinear known factors and integer offsets carry all guards") {
    for(const bool permuted:{false,true}) {
        const VarId x=permuted?5:1,t=permuted?1:2,a=permuted?2:3,b=permuted?3:4,c=permuted?4:5;
        const auto xv=term(1,{{x,1}}),tv=term(1,{{t,1}}),av=term(1,{{a,1}}),
            bv=term(1,{{b,1}}),cv=term(1,{{c,1}});
        auto s=tv+term(1,{});
        auto q=bv*bv-av*cv; // q<=0
        auto p=av*s.pow(10)*xv*xv+cv*s.pow(2)-q*s.pow(7);
        auto cross=s.pow(6)*bv*xv;cross*=2;p-=cross;
        auto tBound=tv-term(1,{});
        for(const bool reverse:{false,true}) {
            auto premise=q; if(reverse)premise*=-1;
            auto target=p; if(reverse)target*=mpq_class(-7,13);
            const Relation relation=reverse?Relation::Gt:Relation::Lt;
            std::vector<SignRefuteConstraint> constraints={con(tBound,Relation::Geq,10),
                con(av,Relation::Geq,20),con(cv,Relation::Geq,30),
                con(premise,reverse?Relation::Geq:Relation::Leq,40),con(target,relation,50)};
            QuadraticSignStatistics stats;
            auto proof=refuteByQuadraticSigns(constraints,&stats);
            REQUIRE(proof.has_value());
            CHECK(stats.factorDivisions>0);
            CHECK_FALSE(stats.exhausted);
            for(unsigned id:{10U,20U,30U,40U,50U})
                CHECK(std::any_of(proof->begin(),proof->end(),[&](SatLit r){return r.var==id;}));
            constraints.back()=con(p+term(1,{}),Relation::Leq,50);
            CHECK(refuteByQuadraticSigns(constraints).has_value());
            constraints.back()=con(p,Relation::Leq,50);
            CHECK_FALSE(refuteByQuadraticSigns(constraints).has_value()); // x=b=c=0 is a boundary model
        }
    }
}

TEST_CASE("quadratic-sign: dropping coefficient or determinant guards leaves SAT models open") {
    const VarId a=3,b=4,c=5;
    const auto av=term(1,{{a,1}}),bv=term(1,{{b,1}}),cv=term(1,{{c,1}});
    auto determinant=av*cv;determinant*=4;determinant-=bv*bv;
    const auto p=av*term(1,{{X,2}})+bv*term(1,{{X,1}})+cv;
    const std::vector<SignRefuteConstraint> guards={con(av,Relation::Geq,10),
        con(cv,Relation::Geq,20),con(determinant,Relation::Geq,30)};
    for(size_t omitted=0;omitted<guards.size();++omitted) {
        std::vector<SignRefuteConstraint> constraints;
        for(size_t i=0;i<guards.size();++i)if(i!=omitted)constraints.push_back(guards[i]);
        constraints.push_back(con(p,Relation::Lt,40));
        CHECK_FALSE(refuteByQuadraticSigns(constraints).has_value());
    }
}
