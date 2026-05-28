#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }

// poly = product-of-vars  (+ optional constant), built from a var-name list
static PolyId mkMonomial(PolynomialKernel& k, std::initializer_list<const char*> vars) {
    PolyId p = k.mkOne();
    for (const char* v : vars) p = k.mul(p, k.mkVar(k.getOrCreateVar(v)));
    return p;
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with a>=0,b>=0 -> a>=1, b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    REQUIRE(ds.getDomain("a") != nullptr);
    REQUIRE(ds.getDomain("b") != nullptr);
    CHECK(ds.getDomain("a")->hasLower);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->hasLower);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with a>=0, b in [0,0] -> Conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addUpperBound("b", mpz_class(0), mkReason(4));  // b pinned to 0

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("ProductPositivity: a*b - 1 >= 0 with b sign UNKNOWN -> NoChange (unsound to fire)") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    // b has no lower bound -> could be negative -> a*b>=1 does NOT imply b>=1

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b"}), kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ProductPositivity: a*b >= 0 (no positive const) -> NoChange") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    PolyId poly = mkMonomial(*kernel, {"a", "b"});  // a*b >= 0, L=0, cannot force >=1
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(3)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ProductPositivity: a*b*c - 1 = 0 with all>=0 -> a,b,c >= 1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));

    PolyId poly = kernel->sub(mkMonomial(*kernel, {"a", "b", "c"}), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
    CHECK(ds.getDomain("c")->lower.value == 1);
}

// --- sign-absorption (milestone 2): one positive monomial, others negative
//     with nonneg factors -> the positive monomial is bounded below. ---

TEST_CASE("SignAbsorption: a*b - c - 1 >= 0 with a,b,c>=0 -> a>=1, b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));

    // a*b - c - 1 >= 0 : positive monomial a*b, negative c (nonneg), const -1
    //  => a*b >= 1 + c >= 1 => a,b >= 1
    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId poly = kernel->sub(kernel->sub(ab, kernel->mkVar(kernel->getOrCreateVar("c"))),
                              kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

TEST_CASE("SignAbsorption: a*b - x - 1 >= 0 with x sign UNKNOWN -> NoChange") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    // x has no lower bound -> -x could be large positive -> a*b need not be >= 1

    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId poly = kernel->sub(kernel->sub(ab, kernel->mkVar(kernel->getOrCreateVar("x"))),
                              kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SignAbsorption: two positive monomials a*b + c*d - 1 >= 0 -> NoChange") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    for (const char* v : {"a", "b", "c", "d"}) ds.addLowerBound(v, mpz_class(0), mkReason(1));

    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId cd = mkMonomial(*kernel, {"c", "d"});
    PolyId poly = kernel->sub(kernel->add(ab, cd), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("SignAbsorption: 2*a*b - c - 3 >= 0 with a,b,c>=0 -> a>=1, b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    for (const char* v : {"a", "b", "c"}) ds.addLowerBound(v, mpz_class(0), mkReason(1));

    // 2*a*b - c - 3 >= 0 => 2*a*b >= 3 => a*b >= 2 => a,b >= 1
    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId twoab = kernel->mul(kernel->mkConst(mpq_class(2)), ab);
    PolyId poly = kernel->sub(kernel->sub(twoab, kernel->mkVar(kernel->getOrCreateVar("c"))),
                              kernel->mkConst(mpq_class(3)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

// --- closer 1 (milestone 3): equality common-factor cancellation.
//     a*f = 0 with a != 0 (established a >= 1) ==> f = 0. ---

TEST_CASE("EqCancel: b*a - a = 0 with a>=1 -> b fixed to 1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(1), mkReason(1));   // a >= 1 (established nonzero)
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    // b*a - a = 0  <=>  a*(b-1) = 0 ; a != 0  =>  b = 1
    PolyId ba = mkMonomial(*kernel, {"b", "a"});
    PolyId poly = kernel->sub(ba, kernel->mkVar(kernel->getOrCreateVar("a")));
    auto cc = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(3)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    REQUIRE(ds.getDomain("b") != nullptr);
    CHECK(ds.getDomain("b")->hasLower);
    CHECK(ds.getDomain("b")->hasUpper);
    CHECK(ds.getDomain("b")->lower.value == 1);
    CHECK(ds.getDomain("b")->upper.value == 1);
}

TEST_CASE("EqCancel: b*a - a = 0 with a possibly 0 (a>=0) -> b NOT fixed (guard)") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));   // a >= 0, could be 0
    ds.addLowerBound("b", mpz_class(0), mkReason(2));

    PolyId ba = mkMonomial(*kernel, {"b", "a"});
    PolyId poly = kernel->sub(ba, kernel->mkVar(kernel->getOrCreateVar("a")));
    auto cc = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(3)};

    auto r = reasoner.run({cc}, ds);
    // a may be 0 -> cancellation unsound -> b must NOT be pinned.
    const IntDomain* db = ds.getDomain("b");
    CHECK((db == nullptr || !db->hasUpper));
}

TEST_CASE("EqCancel fixpoint: [a*c-1>=0, b*a-a=0] with a,b,c>=0 -> a>=1,c>=1,b=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    for (const char* v : {"a", "b", "c"}) ds.addLowerBound(v, mpz_class(0), mkReason(1));

    // sign-absorption on a*c-1>=0 gives a>=1,c>=1; THEN eq-cancel on b*a-a=0
    // (now a>=1) gives b=1 -- requires the rules to chain within one run().
    PolyId ac = mkMonomial(*kernel, {"a", "c"});
    PolyId c1 = kernel->sub(ac, kernel->mkConst(mpq_class(1)));
    PolyId ba = mkMonomial(*kernel, {"b", "a"});
    PolyId c2 = kernel->sub(ba, kernel->mkVar(kernel->getOrCreateVar("a")));

    auto r = reasoner.run({{c1, Relation::Geq, mkReason(2)},
                           {c2, Relation::Eq,  mkReason(3)}}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("c")->lower.value == 1);
    REQUIRE(ds.getDomain("b") != nullptr);
    CHECK(ds.getDomain("b")->hasUpper);
    CHECK(ds.getDomain("b")->lower.value == 1);
    CHECK(ds.getDomain("b")->upper.value == 1);
}

// --- closer 2 (milestone 3): substitution of domain-FIXED vars into monomials.
//     v fixed to val (lower==upper) ==> replace v by val in every poly. ---

TEST_CASE("Substitution: b*a*c - b >= 0 with b fixed=1 -> a>=1, c>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("c", mpz_class(0), mkReason(2));
    ds.addLowerBound("b", mpz_class(1), mkReason(3));
    ds.addUpperBound("b", mpz_class(1), mkReason(4));   // b fixed to 1

    // b*a*c - b >= 0 ; substitute b=1 => a*c - 1 >= 0 => a,c >= 1
    PolyId bac = mkMonomial(*kernel, {"b", "a", "c"});
    PolyId poly = kernel->sub(bac, kernel->mkVar(kernel->getOrCreateVar("b")));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(5)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("c")->lower.value == 1);
}

TEST_CASE("Substitution: a - b = 0 with b>=1 (NOT fixed) -> a NOT pinned") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("b", mpz_class(1), mkReason(1));   // b >= 1 but NO upper -> not fixed
    ds.addLowerBound("a", mpz_class(0), mkReason(2));

    // a - b = 0 ; b is not fixed, so substituting b=1 (wrongly) would pin a=1.
    PolyId poly = kernel->sub(kernel->mkVar(kernel->getOrCreateVar("a")),
                              kernel->mkVar(kernel->getOrCreateVar("b")));
    auto cc = NormalizedNiaConstraint{poly, Relation::Eq, mkReason(3)};

    auto r = reasoner.run({cc}, ds);
    const IntDomain* da = ds.getDomain("a");
    CHECK((da == nullptr || !da->hasUpper));   // a must NOT be pinned to a value
}

// --- closer 3 (milestone 3): monomial dominance -> Conflict.
//     positive M dominated by negative M'=M*E (E factors established >=1) with
//     base M>=0 established, plus constant < 0  ==>  LHS <= d < 0  ==> UNSAT. ---

TEST_CASE("Dominance: a*b - a*b*c - 1 >= 0 with a,b>=0, c>=1 -> Conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(1), mkReason(3));   // c >= 1 (the extra factor)

    // a*b - a*b*c - 1 >= 0 : a*b*c = (a*b)*c >= a*b (c>=1, a*b>=0)
    //   => a*b - a*b*c <= 0 => LHS <= -1 < 0  => UNSAT
    PolyId ab  = mkMonomial(*kernel, {"a", "b"});
    PolyId abc = mkMonomial(*kernel, {"a", "b", "c"});
    PolyId poly = kernel->sub(kernel->sub(ab, abc), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("Dominance guard: base sign unknown (a no lower) -> NO false conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    // a has NO lower bound: a*b could be negative, then a*b*c <= a*b (flip) and
    // a=-2,b=1,c=2 satisfies a*b - a*b*c - 1 = -2+4-1 = 1 >= 0.  Must NOT refute.
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(1), mkReason(3));

    PolyId ab  = mkMonomial(*kernel, {"a", "b"});
    PolyId abc = mkMonomial(*kernel, {"a", "b", "c"});
    PolyId poly = kernel->sub(kernel->sub(ab, abc), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind != NiaReasoningKind::Conflict);
}

TEST_CASE("Dominance guard: extra factor not >=1 (c could be 0) -> NO false conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));   // c >= 0: c=0 => a*b-1>=0 satisfiable

    PolyId ab  = mkMonomial(*kernel, {"a", "b"});
    PolyId abc = mkMonomial(*kernel, {"a", "b", "c"});
    PolyId poly = kernel->sub(kernel->sub(ab, abc), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind != NiaReasoningKind::Conflict);
}

// The NiaNormalizer emits constraints in `poly <= 0` (Leq) form, so the rules
// must handle Leq by negating. Same dominance contradiction, Leq-encoded.
TEST_CASE("Dominance (Leq form): a*b*c - a*b + 1 <= 0 with a,b>=0,c>=1 -> Conflict") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(1), mkReason(3));

    // a*b*c - a*b + 1 <= 0  ==  -(a*b - a*b*c - 1) <= 0  ==  a*b - a*b*c - 1 >= 0
    PolyId ab  = mkMonomial(*kernel, {"a", "b"});
    PolyId abc = mkMonomial(*kernel, {"a", "b", "c"});
    PolyId poly = kernel->add(kernel->sub(abc, ab), kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("SignAbsorption (Leq form): -a*b + c + 1 <= 0 with a,b,c>=0 -> a>=1,b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    for (const char* v : {"a", "b", "c"}) ds.addLowerBound(v, mpz_class(0), mkReason(1));

    // -a*b + c + 1 <= 0  ==  a*b - c - 1 >= 0  =>  a,b >= 1
    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId poly = kernel->add(kernel->add(kernel->neg(ab),
                              kernel->mkVar(kernel->getOrCreateVar("c"))),
                              kernel->mkConst(mpq_class(1)));
    auto cc = NormalizedNiaConstraint{poly, Relation::Leq, mkReason(4)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

// --- milestone 4: sign-absorption uses absorbed monomials' LOWER bounds.
//     M+ >= -d + sum |cj| * lb(mj)  (lb(mj) = product of factor lower bounds). ---

TEST_CASE("SignAbsorptionLB: a*b - c*d >= 0 with a,b>=0, c>=1, d>=1 -> a>=1, b>=1") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(1), mkReason(3));
    ds.addLowerBound("d", mpz_class(1), mkReason(4));

    // a*b - c*d >= 0 : c*d >= 1 (c,d>=1) => a*b >= 1 => a,b >= 1
    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId cd = mkMonomial(*kernel, {"c", "d"});
    PolyId poly = kernel->sub(ab, cd);
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(5)};

    auto r = reasoner.run({cc}, ds);
    CHECK(r.kind == NiaReasoningKind::DomainUpdated);
    CHECK(ds.getDomain("a")->lower.value == 1);
    CHECK(ds.getDomain("b")->lower.value == 1);
}

TEST_CASE("SignAbsorptionLB: a*b - c*d >= 0 with c>=0 (could be 0) -> no false derive") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));   // c may be 0 -> c*d lb = 0
    ds.addLowerBound("d", mpz_class(1), mkReason(4));

    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId cd = mkMonomial(*kernel, {"c", "d"});
    PolyId poly = kernel->sub(ab, cd);
    auto cc = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(5)};

    auto r = reasoner.run({cc}, ds);
    // c*d lower bound is 0, so only a*b >= 0 -> cannot force a,b >= 1
    const IntDomain* da = ds.getDomain("a");
    CHECK((da == nullptr || !da->hasLower || da->lower.value < 1));
}

TEST_CASE("ProductPositivity: multi-monomial a*b + c - 1 >= 0 -> NoChange (milestone 1)") {
    auto kernel = createPolynomialKernel();
    ProductPositivityReasoner reasoner(*kernel);
    DomainStore ds;
    ds.addLowerBound("a", mpz_class(0), mkReason(1));
    ds.addLowerBound("b", mpz_class(0), mkReason(2));
    ds.addLowerBound("c", mpz_class(0), mkReason(3));

    PolyId ab = mkMonomial(*kernel, {"a", "b"});
    PolyId poly = kernel->sub(kernel->add(ab, kernel->mkVar(kernel->getOrCreateVar("c"))),
                              kernel->mkConst(mpq_class(1)));
    auto c = NormalizedNiaConstraint{poly, Relation::Geq, mkReason(4)};

    auto r = reasoner.run({c}, ds);
    CHECK(r.kind == NiaReasoningKind::NoChange);
}
