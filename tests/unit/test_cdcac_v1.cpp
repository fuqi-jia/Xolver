#include <doctest/doctest.h>
#include <iostream>
#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/projection/LocalProjection.h"

using namespace nlcolver;

TEST_CASE("resultant: y - x^2 and y w.r.t. y") {
    VarId x = 1, y = 2;
    
    // p = y - x^2
    auto p = RationalPolynomial::fromVar(y, 1, mpq_class(1))
           + RationalPolynomial::fromVar(x, 2, mpq_class(-1));
    
    // q = y
    auto q = RationalPolynomial::fromVar(y, 1, mpq_class(1));
    
    // Debug: print coefficients
    auto pc = p.coefficients(y);
    auto qc = q.coefficients(y);
    std::cout << "p.coeffs(y): ";
    for (size_t i = 0; i < pc.size(); ++i) {
        std::cout << "[" << i << "]=";
        for (const auto& [k, c] : pc[i].terms()) {
            std::cout << c.get_str() << " ";
        }
    }
    std::cout << std::endl;
    std::cout << "q.coeffs(y): ";
    for (size_t i = 0; i < qc.size(); ++i) {
        std::cout << "[" << i << "]=";
        for (const auto& [k, c] : qc[i].terms()) {
            std::cout << c.get_str() << " ";
        }
    }
    std::cout << std::endl;
    
    auto r = resultant(p, q, y);
    
    std::cout << "resultant terms: ";
    for (const auto& [key, coeff] : r.terms()) {
        std::cout << coeff.get_str() << " * ";
        for (const auto& [v, e] : key) {
            std::cout << "v" << v << "^" << e;
        }
        std::cout << " | ";
    }
    std::cout << std::endl;
    
    // Expected: x^2 (or -x^2 depending on convention)
    CHECK(r.terms().size() == 1);
    auto it = r.terms().begin();
    CHECK(it->first.size() == 1);
    CHECK(it->first[0].first == x);
    CHECK(it->first[0].second == 2);
}

TEST_CASE("resultant: x^2 + y^2 - 1 and y - x w.r.t. y") {
    VarId x = 1, y = 2;
    
    // p = x^2 + y^2 - 1
    auto p = RationalPolynomial::fromVar(x, 2, mpq_class(1))
           + RationalPolynomial::fromVar(y, 2, mpq_class(1))
           + RationalPolynomial::fromConstant(mpq_class(-1));
    
    // q = y - x
    auto q = RationalPolynomial::fromVar(y, 1, mpq_class(1))
           + RationalPolynomial::fromVar(x, 1, mpq_class(-1));
    
    auto r = resultant(p, q, y);
    
    std::cout << "resultant2 terms: ";
    for (const auto& [key, coeff] : r.terms()) {
        std::cout << coeff.get_str() << " * ";
        for (const auto& [v, e] : key) {
            std::cout << "v" << v << "^" << e;
        }
        std::cout << " | ";
    }
    std::cout << std::endl;
    
    // Expected: 2x^2 - 1
    CHECK(r.terms().size() == 2);
}

TEST_CASE("LocalProjection: basic carry-down") {
    VarId x = 1, y = 2;
    
    // p = x + 1 (does not contain y)
    auto p = RationalPolynomial::fromVar(x, 1, mpq_class(1))
           + RationalPolynomial::fromConstant(mpq_class(1));
    
    LocalProjectionEngine engine;
    std::vector<ReasonedPolynomial> input = {
        {p, PolyRole::ConstraintPolynomial, {SatLit{1, true}}}
    };
    
    auto result = engine.project(input, y);
    
    CHECK(!result.hasDegeneracy);
    CHECK(result.polys.size() == 1);
    CHECK(!result.polys[0].poly.contains(y));
}
