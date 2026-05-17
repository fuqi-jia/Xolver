#include <gmpxx.h>
#include <doctest/doctest.h>
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/ir.h"
#include <chrono>

using namespace nlcolver;
using namespace std::chrono;

// Helper: measure time in milliseconds
static double elapsedMs(steady_clock::time_point start) {
    return duration<double, std::milli>(steady_clock::now() - start).count();
}

// ============================================================================
// High-degree univariate / binomial expansion
// ============================================================================

TEST_CASE("Stress: (x+y)^50 binomial expansion") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1));
    rp += RationalPolynomial::fromVar(yv, 1, mpq_class(1));

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(50);
    double ms = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 51);  // C(51,50) = 51 terms
    CHECK(expanded.terms().at(MonomialKey{{xv, 50}}) == mpq_class(1));
    CHECK(expanded.terms().at(MonomialKey{{yv, 50}}) == mpq_class(1));

    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());
    CHECK(norm.scale == 1);

    // Verify at x=1, y=1: (1+1)^50 = 2^50
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 1}});
    REQUIRE(valOpt.has_value());
    mpz_class expected;
    mpz_ui_pow_ui(expected.get_mpz_t(), 2, 50);
    CHECK(*valOpt == expected);

    CAPTURE(ms);
    CHECK(ms < 5000.0);  // should complete within 5 seconds
}

// ============================================================================
// Multivariate high-degree expansion
// ============================================================================

TEST_CASE("Stress: (x+y+z)^20  trinomial expansion") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");
    VarId zv = kernel->getOrCreateVar("z");

    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1));
    rp += RationalPolynomial::fromVar(yv, 1, mpq_class(1));
    rp += RationalPolynomial::fromVar(zv, 1, mpq_class(1));

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(20);
    double ms = elapsedMs(t0);

    // Number of terms = C(3+20-1, 20) = C(22, 20) = 231
    REQUIRE(expanded.terms().size() == 231);

    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at x=1, y=1, z=1: (1+1+1)^20 = 3^20
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 1}, {zv, 1}});
    REQUIRE(valOpt.has_value());
    mpz_class expected;
    mpz_ui_pow_ui(expected.get_mpz_t(), 3, 20);
    CHECK(*valOpt == expected);

    CAPTURE(ms);
    CHECK(ms < 10000.0);  // within 10 seconds
}

TEST_CASE("Stress: (x+y+z+w+u)^10  5-var expansion") {
    auto kernel = createPolynomialKernel();
    VarId v[5];
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    RationalPolynomial rp;
    for (int i = 0; i < 5; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, mpq_class(1));
    }

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(10);
    double ms = elapsedMs(t0);

    // C(5+10-1, 10) = C(14, 10) = 1001 terms
    REQUIRE(expanded.terms().size() == 1001);

    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at all-ones: 5^10 = 9765625
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    mpz_class expected;
    mpz_ui_pow_ui(expected.get_mpz_t(), 5, 10);
    CHECK(*valOpt == expected);

    CAPTURE(ms);
    CHECK(ms < 15000.0);
}

// ============================================================================
// Large-denominator LCM stress
// ============================================================================

TEST_CASE("Stress: large denominator LCM (1/2*x + 1/3*y + 1/5*z + 1/7*w + 1/11*u)^10") {
    auto kernel = createPolynomialKernel();
    VarId v[5];
    mpq_class coeffs[5] = {
        mpq_class(1, 2), mpq_class(1, 3), mpq_class(1, 5),
        mpq_class(1, 7), mpq_class(1, 11)
    };
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    RationalPolynomial rp;
    for (int i = 0; i < 5; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, coeffs[i]);
    }

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(10);
    double ms1 = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 1001);

    auto t1 = steady_clock::now();
    auto norm = expanded.toPrimitiveInteger(*kernel);
    double ms2 = elapsedMs(t1);

    REQUIRE(norm.ok());
    // D = lcm(2^10, 3^10, 5^10, 7^10, 11^10) = 2^10 * 3^10 * 5^10 * 7^10 * 11^10
    // scale = g/D where g = gcd of all integer coefficients
    // scale should be positive and canonical
    CHECK(norm.scale > 0);

    // Verify at all-ones: (1/2 + 1/3 + 1/5 + 1/7 + 1/11)^10
    // = (1155/2310 + 770/2310 + 462/2310 + 330/2310 + 210/2310)^10
    // = (2927/2310)^10
    mpq_class base(2927, 2310);
    mpq_class expectedVal = base;
    for (int i = 1; i < 10; ++i) expectedVal *= base;

    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actualVal(*valOpt);
    actualVal *= norm.scale;
    CHECK(actualVal == expectedVal);

    CAPTURE(ms1);
    CAPTURE(ms2);
    CHECK(ms1 < 15000.0);
    CHECK(ms2 < 10000.0);
}

// ============================================================================
// Long multiplication chain
// ============================================================================

TEST_CASE("Stress: v0 * v1 * ... * v19  (20-variable product)") {
    auto kernel = createPolynomialKernel();
    RationalPolynomial rp = RationalPolynomial::fromConstant(mpq_class(1));
    VarId vars[20];
    for (int i = 0; i < 20; ++i) {
        vars[i] = kernel->getOrCreateVar("v" + std::to_string(i));
        rp = rp * RationalPolynomial::fromVar(vars[i], 1, mpq_class(1));
    }

    REQUIRE(rp.terms().size() == 1);
    CHECK(rp.terms().begin()->first.size() == 20);

    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at all-ones: 1
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 20; ++i) sample[vars[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 1);
}

// ============================================================================
// Cascaded rational substitution
// ============================================================================

TEST_CASE("Stress: cascaded substituteRational (x+y)^10, x=1/2, y=1/3") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    // Build (x+y)^10 as integer poly
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1));
    rp += RationalPolynomial::fromVar(yv, 1, mpq_class(1));
    auto norm = rp.pow(10).toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Substitute x = 1/2
    auto sub1 = kernel->substituteRational(norm.poly, xv, mpq_class(1, 2));
    REQUIRE(sub1.has_value());

    // Substitute y = 1/3 into result
    auto sub2 = kernel->substituteRational(*sub1, yv, mpq_class(1, 3));
    REQUIRE(sub2.has_value());

    // After two rational substitutions, result should be a constant polynomial.
    // Note: toConstant returns the primitive integer value; the true rational
    // value is primitive-value * scale.  Without explicit scale tracking in
    // PolyId, we only verify the result is constant and non-zero here.
    CHECK(kernel->isConstant(*sub2));
    CHECK(!kernel->isZero(*sub2));

    // Verify sign is positive (true value (5/6)^10 > 0)
    mpq_class constVal = kernel->toConstant(*sub2);
    CHECK(constVal > 0);
}

// ============================================================================
// Deeply nested expression from CoreIr
// ============================================================================

TEST_CASE("Stress: PolynomialConverter deep nested rational expression") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    // Build: ((1/2)*v0 + (1/3)*v1 + (1/5)*v2 + (1/7)*v3 + (1/11)*v4)^8
    VarId v[5];
    mpq_class coeffs[5] = {
        mpq_class(1, 2), mpq_class(1, 3), mpq_class(1, 5),
        mpq_class(1, 7), mpq_class(1, 11)
    };
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    ExprId terms[5];
    for (int i = 0; i < 5; ++i) {
        ExprId vi = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("v") + std::to_string(i))});
        ExprId ci = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string(coeffs[i].get_str()))});
        terms[i] = ir.add(CoreExpr{Kind::Mul, 0, {ci, vi}, {}});
    }
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {terms[0], terms[1], terms[2], terms[3], terms[4]}, {}});
    ExprId eight = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(8))});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {addExpr, eight}, {}});

    auto t0 = steady_clock::now();
    auto res = conv.convert(powExpr, ir);
    double ms = elapsedMs(t0);

    REQUIRE(res.ok());
    CHECK(res.scale > 0);

    // Verify at all-ones
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(res.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= res.scale;
    mpq_class expected(2927, 2310);
    for (int i = 1; i < 8; ++i) expected *= mpq_class(2927, 2310);
    CHECK(actual == expected);

    CAPTURE(ms);
    CHECK(ms < 20000.0);
}

// ============================================================================
// Content-gcd stress with many terms
// ============================================================================

TEST_CASE("Stress: large content gcd (2/6*x + 4/6*y + 6/6*z + 8/6*w + 10/6*u)^5") {
    auto kernel = createPolynomialKernel();
    VarId v[5];
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    RationalPolynomial rp;
    for (int i = 0; i < 5; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, mpq_class(2*(i+1), 6));
    }

    auto expanded = rp.pow(5);
    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at all-ones: (2/6 + 4/6 + 6/6 + 8/6 + 10/6)^5 = (30/6)^5 = 5^5 = 3125
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= norm.scale;
    CHECK(actual == mpq_class(3125));
}

// ============================================================================
// ULTRA STRESS TESTS -- these push the system hard
// ============================================================================

TEST_CASE("ULTRA: (x+y)^100  massive binomial coefficients") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1));
    rp += RationalPolynomial::fromVar(yv, 1, mpq_class(1));

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(100);
    double ms1 = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 101);
    // Middle coefficient C(100,50) ~ 1e29
    MonomialKey midKey{{xv, 50}, {yv, 50}};
    auto it = expanded.terms().find(midKey);
    REQUIRE(it != expanded.terms().end());
    mpz_class expectedMid;
    mpz_bin_uiui(expectedMid.get_mpz_t(), 100, 50);
    CHECK(it->second == mpq_class(expectedMid));

    auto t1 = steady_clock::now();
    auto norm = expanded.toPrimitiveInteger(*kernel);
    double ms2 = elapsedMs(t1);
    REQUIRE(norm.ok());

    // Verify at x=1, y=1: 2^100
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 1}});
    REQUIRE(valOpt.has_value());
    mpz_class expected;
    mpz_ui_pow_ui(expected.get_mpz_t(), 2, 100);
    CHECK(*valOpt == expected);

    CAPTURE(ms1);
    CAPTURE(ms2);
    CHECK(ms1 < 5000.0);
    CHECK(ms2 < 5000.0);
}

TEST_CASE("ULTRA: 30-variable sum cubed  (v0+...+v29)^3") {
    auto kernel = createPolynomialKernel();
    const int N = 30;
    std::vector<VarId> vars;
    vars.reserve(N);
    RationalPolynomial rp;
    for (int i = 0; i < N; ++i) {
        vars.push_back(kernel->getOrCreateVar("v" + std::to_string(i)));
        rp += RationalPolynomial::fromVar(vars.back(), 1, mpq_class(1));
    }

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(3);
    double ms1 = elapsedMs(t0);

    // Number of terms = C(30+3-1, 3) = C(32,3) = 4960
    REQUIRE(expanded.terms().size() == 4960);

    auto t1 = steady_clock::now();
    auto norm = expanded.toPrimitiveInteger(*kernel);
    double ms2 = elapsedMs(t1);
    REQUIRE(norm.ok());

    // Verify at all-ones: 30^3 = 27000
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < N; ++i) sample[vars[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == mpz_class(27000));

    CAPTURE(ms1);
    CAPTURE(ms2);
    CHECK(ms1 < 5000.0);
    CHECK(ms2 < 10000.0);
}

TEST_CASE("ULTRA: large prime denominators (1/997*x + 1/991*y + 1/983*z + 1/977*w + 1/971*u)^8") {
    auto kernel = createPolynomialKernel();
    VarId v[5];
    // Five consecutive large primes
    mpq_class coeffs[5] = {
        mpq_class(1, 997), mpq_class(1, 991), mpq_class(1, 983),
        mpq_class(1, 977), mpq_class(1, 971)
    };
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    RationalPolynomial rp;
    for (int i = 0; i < 5; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, coeffs[i]);
    }

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(8);
    double ms1 = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 495); // C(5+8-1, 8) = C(12,8) = 495

    auto t1 = steady_clock::now();
    auto norm = expanded.toPrimitiveInteger(*kernel);
    double ms2 = elapsedMs(t1);
    REQUIRE(norm.ok());

    // D = lcm(997^8, 991^8, 983^8, 977^8, 971^8) = product (all distinct primes)
    // This is a ~40-digit number. LCM computation must handle it.
    CHECK(norm.scale > 0);

    // Verify at all-ones
    mpq_class base;
    for (int i = 0; i < 5; ++i) base += coeffs[i];
    mpq_class expectedVal = base;
    for (int i = 1; i < 8; ++i) expectedVal *= base;

    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= norm.scale;
    CHECK(actual == expectedVal);

    CAPTURE(ms1);
    CAPTURE(ms2);
    CHECK(ms1 < 15000.0);
    CHECK(ms2 < 15000.0);
}

TEST_CASE("ULTRA: 10-level cascaded substitution") {
    auto kernel = createPolynomialKernel();
    const int N = 10;
    std::vector<VarId> vars;
    vars.reserve(N);
    RationalPolynomial rp = RationalPolynomial::fromConstant(mpq_class(1));
    for (int i = 0; i < N; ++i) {
        vars.push_back(kernel->getOrCreateVar("v" + std::to_string(i)));
        rp += RationalPolynomial::fromVar(vars.back(), 1, mpq_class(1));
    }
    // P = 1 + v0 + v1 + ... + v9
    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Cascaded substitution: substitute each vi = 1/(i+2)
    // Final value = 1 + sum_{i=0}^{9} 1/(i+2) = 1 + 1/2 + 1/3 + ... + 1/11
    mpq_class expectedVal(1);
    for (int i = 0; i < N; ++i) expectedVal += mpq_class(1, i + 2);

    auto t0 = steady_clock::now();
    PolyId current = norm.poly;
    for (int i = 0; i < N; ++i) {
        auto nextOpt = kernel->substituteRational(current, vars[i], mpq_class(1, i + 2));
        REQUIRE(nextOpt.has_value());
        current = *nextOpt;
    }
    double ms = elapsedMs(t0);

    CHECK(kernel->isConstant(current));
    mpq_class constVal = kernel->toConstant(current);
    CHECK(constVal > 0);

    CAPTURE(ms);
    CHECK(ms < 10000.0);
}

TEST_CASE("ULTRA: consecutive prime fraction coefficients to power 15") {
    auto kernel = createPolynomialKernel();
    VarId v[6];
    // Coefficients: 2/3, 3/5, 5/7, 7/11, 11/13, 13/17
    mpq_class coeffs[6] = {
        mpq_class(2, 3), mpq_class(3, 5), mpq_class(5, 7),
        mpq_class(7, 11), mpq_class(11, 13), mpq_class(13, 17)
    };
    for (int i = 0; i < 6; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    RationalPolynomial rp;
    for (int i = 0; i < 6; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, coeffs[i]);
    }

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(15);
    double ms1 = elapsedMs(t0);

    // C(6+15-1, 15) = C(20, 15) = 15504 terms
    REQUIRE(expanded.terms().size() == 15504);

    auto t1 = steady_clock::now();
    auto norm = expanded.toPrimitiveInteger(*kernel);
    double ms2 = elapsedMs(t1);
    REQUIRE(norm.ok());

    // Verify at all-ones
    mpq_class base;
    for (int i = 0; i < 6; ++i) base += coeffs[i];
    mpq_class expectedVal = base;
    for (int i = 1; i < 15; ++i) expectedVal *= base;

    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 6; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= norm.scale;
    CHECK(actual == expectedVal);

    CAPTURE(ms1);
    CAPTURE(ms2);
    CHECK(ms1 < 20000.0);
    CHECK(ms2 < 20000.0);
}

TEST_CASE("ULTRA: massive content gcd  10^6 * (x + y + z + w + u)") {
    auto kernel = createPolynomialKernel();
    VarId v[5];
    for (int i = 0; i < 5; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    mpz_class big("1000000000000"); // 10^12
    RationalPolynomial rp;
    for (int i = 0; i < 5; ++i) {
        rp += RationalPolynomial::fromVar(v[i], 1, mpq_class(big));
    }

    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // All coefficients share gcd = 10^12, so the primitive poly should
    // have coefficients = 1 and scale = 10^12
    CHECK(norm.scale == mpq_class(big));

    // Verify at all-ones: 5 * 10^12
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 5; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(norm.poly, sample);
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == mpz_class(5));
}

TEST_CASE("ULTRA: alternating sign high power  (-x + y)^50") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(-1));
    rp += RationalPolynomial::fromVar(yv, 1, mpq_class(1));

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(50);
    double ms = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 51);

    // Alternating binomial coefficients: C(50,k) * (-1)^k for x^k y^(50-k)
    for (int k = 0; k <= 50; ++k) {
        MonomialKey key;
        if (k > 0) key.push_back({xv, k});
        if (50 - k > 0) key.push_back({yv, 50 - k});
        auto it = expanded.terms().find(key);
        REQUIRE(it != expanded.terms().end());
        mpz_class binom;
        mpz_bin_uiui(binom.get_mpz_t(), 50, static_cast<unsigned long>(k));
        mpq_class expectedCoeff(binom);
        if (k % 2 != 0) expectedCoeff = -expectedCoeff;
        CHECK(it->second == expectedCoeff);
    }

    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at x=1, y=1: (-1+1)^50 = 0
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 1}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 0);

    // Verify at x=1, y=2: (-1+2)^50 = 1
    valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 2}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 1);

    CAPTURE(ms);
    CHECK(ms < 5000.0);
}

TEST_CASE("ULTRA: monomial power tower  (x^2 * y^3 * z^5)^20") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");
    VarId zv = kernel->getOrCreateVar("z");

    RationalPolynomial rp = RationalPolynomial::fromVar(xv, 2, mpq_class(1));
    rp = rp * RationalPolynomial::fromVar(yv, 3, mpq_class(1));
    rp = rp * RationalPolynomial::fromVar(zv, 5, mpq_class(1));

    auto t0 = steady_clock::now();
    auto expanded = rp.pow(20);
    double ms = elapsedMs(t0);

    REQUIRE(expanded.terms().size() == 1);
    auto it = expanded.terms().begin();
    CHECK(it->first.size() == 3);
    int xExp = 0, yExp = 0, zExp = 0;
    for (const auto& [vid, e] : it->first) {
        if (vid == xv) xExp = e;
        if (vid == yv) yExp = e;
        if (vid == zv) zExp = e;
    }
    CHECK(xExp == 40);
    CHECK(yExp == 60);
    CHECK(zExp == 100);
    CHECK(it->second == mpq_class(1));

    auto norm = expanded.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Verify at x=1, y=1, z=1: 1
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 1}, {yv, 1}, {zv, 1}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 1);

    CAPTURE(ms);
    CHECK(ms < 2000.0);
}

TEST_CASE("ULTRA: deep nested add-mul chain with rationals") {
    auto kernel = createPolynomialKernel();
    CoreIr ir;
    PolynomialConverter conv(*kernel);

    // Build: ((1/2)v0 + (1/3)v1) * ((1/5)v2 + (1/7)v3) * ((1/11)v4 + (1/13)v5)
    VarId v[6];
    mpq_class coeffs[6] = {
        mpq_class(1, 2), mpq_class(1, 3), mpq_class(1, 5),
        mpq_class(1, 7), mpq_class(1, 11), mpq_class(1, 13)
    };
    for (int i = 0; i < 6; ++i) {
        v[i] = kernel->getOrCreateVar("v" + std::to_string(i));
    }

    auto makeMul = [&](int i) -> ExprId {
        ExprId vi = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("v") + std::to_string(i))});
        ExprId ci = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string(coeffs[i].get_str()))});
        return ir.add(CoreExpr{Kind::Mul, 0, {ci, vi}, {}});
    };

    ExprId add0 = ir.add(CoreExpr{Kind::Add, 0, {makeMul(0), makeMul(1)}, {}});
    ExprId add1 = ir.add(CoreExpr{Kind::Add, 0, {makeMul(2), makeMul(3)}, {}});
    ExprId add2 = ir.add(CoreExpr{Kind::Add, 0, {makeMul(4), makeMul(5)}, {}});
    ExprId mul0 = ir.add(CoreExpr{Kind::Mul, 0, {add0, add1}, {}});
    ExprId expr  = ir.add(CoreExpr{Kind::Mul, 0, {mul0, add2}, {}});

    auto t0 = steady_clock::now();
    auto res = conv.convert(expr, ir);
    double ms = elapsedMs(t0);

    REQUIRE(res.ok());
    CHECK(res.scale > 0);

    // Verify at all-ones: (1/2+1/3)*(1/5+1/7)*(1/11+1/13)
    // = (5/6)*(12/35)*(24/143) = (5*12*24)/(6*35*143) = 1440/30030 = 48/1001
    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < 6; ++i) sample[v[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(res.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= res.scale;
    CHECK(actual == mpq_class(48, 1001));

    CAPTURE(ms);
    CHECK(ms < 5000.0);
}

TEST_CASE("ULTRA: PolynomialConverter with 30-variable linear expression squared") {
    auto kernel = createPolynomialKernel();
    CoreIr ir;
    PolynomialConverter conv(*kernel);

    const int N = 30;
    std::vector<VarId> vars;
    vars.reserve(N);
    std::vector<ExprId> children;
    children.reserve(N);

    for (int i = 0; i < N; ++i) {
        vars.push_back(kernel->getOrCreateVar("v" + std::to_string(i)));
        ExprId vi = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("v") + std::to_string(i))});
        ExprId ci = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string(mpq_class(i+1, i+2).get_str()))});
        children.push_back(ir.add(CoreExpr{Kind::Mul, 0, {ci, vi}, {}}));
    }

    SmallVector<ExprId, 4> addChildren;
    for (auto c : children) addChildren.push_back(c);
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, addChildren, {}});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {addExpr, two}, {}});

    auto t0 = steady_clock::now();
    auto res = conv.convert(powExpr, ir);
    double ms = elapsedMs(t0);

    REQUIRE(res.ok());
    CHECK(res.scale > 0);

    // Number of terms in square of n-term sum = C(n+1, 2) + n = n(n+1)/2 + n = n(n+3)/2
    // For n=30: 30*33/2 = 495 terms (cross) + 30 diagonals = but actually
    // a sum of n terms squared has C(n,2) cross terms + n diagonal = n(n+1)/2 = 465 terms
    // The RationalPolynomial should have exactly 465 terms.

    // Verify at all-ones: (sum_{i=1}^{30} i/(i+1))^2
    mpq_class sum(0);
    for (int i = 0; i < N; ++i) sum += mpq_class(i + 1, i + 2);
    mpq_class expectedVal = sum * sum;

    std::unordered_map<VarId, mpz_class> sample;
    for (int i = 0; i < N; ++i) sample[vars[i]] = 1;
    auto valOpt = kernel->evalIntegerVarId(res.poly, sample);
    REQUIRE(valOpt.has_value());
    mpq_class actual(*valOpt);
    actual *= res.scale;
    CHECK(actual == expectedVal);

    CAPTURE(ms);
    CHECK(ms < 15000.0);
}
