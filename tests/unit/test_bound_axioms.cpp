#include "doctest/doctest.h"
#include "theory/arith/linear/BoundAxiomGenerator.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>

using namespace xolver;

namespace {

// Ground-truth: is (L rel c) true at L = x ?
bool atomTrue(Relation rel, const mpq_class& c, const mpq_class& x) {
    switch (rel) {
        case Relation::Leq: return x <= c;
        case Relation::Lt:  return x <  c;
        case Relation::Geq: return x >= c;
        case Relation::Gt:  return x >  c;
        case Relation::Eq:  return x == c;
        case Relation::Neq: return x != c;
        default: return false;
    }
}

// Truth functions change only at the constants, so sampling each constant
// exactly plus points a quarter-unit either side plus far extremes is an
// exhaustive characterization (test constants are integers => gaps >= 1).
std::vector<mpq_class> gridFor(const std::vector<mpq_class>& consts) {
    std::vector<mpq_class> g;
    mpq_class q(1, 4);
    for (const auto& c : consts) { g.push_back(c); g.push_back(c - q); g.push_back(c + q); }
    g.push_back(mpq_class(-1000));
    g.push_back(mpq_class(1000));
    return g;
}

} // namespace

TEST_CASE("BoundAxiomGenerator: every emitted clause shape is a real tautology") {
    using Shape = BoundAxiomGenerator::Shape;
    std::vector<Relation> rels = {Relation::Leq, Relation::Lt, Relation::Geq,
                                  Relation::Gt, Relation::Eq};
    std::vector<mpq_class> consts = {mpq_class(-2), mpq_class(-1), mpq_class(0),
                                     mpq_class(1), mpq_class(2)};
    auto grid = gridFor(consts);

    int totalShapes = 0;
    for (Relation rA : rels) {
        for (const auto& cA : consts) {
            for (Relation rB : rels) {
                for (const auto& cB : consts) {
                    auto shapes = BoundAxiomGenerator::pairShapes(rA, cA, rB, cB);
                    for (Shape s : shapes) {
                        ++totalShapes;
                        for (const auto& x : grid) {
                            bool a = atomTrue(rA, cA, x);
                            bool b = atomTrue(rB, cB, x);
                            bool ok = true;
                            switch (s) {
                                case Shape::ImpAtoB:   ok = !(a && !b); break; // a => b
                                case Shape::ImpBtoA:   ok = !(b && !a); break; // b => a
                                case Shape::Exclusion: ok = !(a && b);  break; // ¬(a∧b)
                                case Shape::Cover:     ok = (a || b);   break; // a∨b
                            }
                            INFO("rA=", (int)rA, " cA=", cA.get_str(),
                                 " rB=", (int)rB, " cB=", cB.get_str(),
                                 " shape=", (int)s, " x=", x.get_str());
                            CHECK(ok);
                        }
                    }
                }
            }
        }
    }
    // Sanity: the generator actually finds relationships (not vacuously empty).
    CHECK(totalShapes > 0);
}

TEST_CASE("BoundAxiomGenerator: known relationships are detected") {
    using Shape = BoundAxiomGenerator::Shape;
    auto has = [](const std::vector<Shape>& v, Shape s) {
        for (Shape x : v) if (x == s) return true;
        return false;
    };

    // (L <= 3) => (L <= 5)
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Leq, 3, Relation::Leq, 5),
              Shape::ImpAtoB));
    // (L <= 3) and (L >= 5) mutually exclusive
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Leq, 3, Relation::Geq, 5),
              Shape::Exclusion));
    // (L <= 3) or (L >= 1) covers ℝ
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Leq, 3, Relation::Geq, 1),
              Shape::Cover));
    // (L < 3) and (L >= 3): exclusion (touch, both not closed-overlapping)
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Lt, 3, Relation::Geq, 3),
              Shape::Exclusion));
    // (L <= 3) or (L > 3): covers ℝ (closed-meets-open at 3, no gap)
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Leq, 3, Relation::Gt, 3),
              Shape::Cover));
    // (L < 3) or (L > 3): does NOT cover (3 uncovered)
    CHECK_FALSE(has(BoundAxiomGenerator::pairShapes(Relation::Lt, 3, Relation::Gt, 3),
                    Shape::Cover));
    // (L = 3) => (L <= 5)
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Eq, 3, Relation::Leq, 5),
              Shape::ImpAtoB));
    // (L = 3) and (L >= 5): exclusion
    CHECK(has(BoundAxiomGenerator::pairShapes(Relation::Eq, 3, Relation::Geq, 5),
              Shape::Exclusion));
    // Neq is unhandled -> no shapes
    CHECK(BoundAxiomGenerator::pairShapes(Relation::Neq, 3, Relation::Leq, 5).empty());
}
