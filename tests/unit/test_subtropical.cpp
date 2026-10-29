// Subtropical candidate finder (search/nra/reasoners/SubtropicalSatFinder).
// The finder is INCOMPLETE and produces only a candidate
// direction; soundness is the caller's job (exact validation). These tests
// check that (a) when it reports `found`, the materialized assignment really
// satisfies every constraint for a large enough base, (b) it bails on
// equalities, and (c) it does not "find" obviously-unsatisfiable shapes.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "search/nra/reasoners/SubtropicalSatFinder.h"

using namespace xolver;

static const VarId X = VarId{1}, Y = VarId{2}, Z = VarId{3};

static SubtropicalMonomial mono(long c, std::vector<std::pair<VarId, int>> p) {
    return SubtropicalMonomial{mpz_class(c), std::move(p)};
}

// Exact value of a constraint polynomial at a rational model.
static mpq_class evalPoly(const SubtropicalConstraint& c,
                          const std::unordered_map<VarId, mpq_class>& m) {
    mpq_class total(0);
    for (const auto& mm : c.monomials) {
        mpq_class term(mm.coeff);
        for (const auto& [v, e] : mm.powers) {
            mpq_class base = m.at(v);
            for (int k = 0; k < e; ++k) term *= base;
        }
        total += term;
    }
    return total;
}

static bool relHolds(Relation rel, const mpq_class& v) {
    switch (rel) {
        case Relation::Eq:  return sgn(v) == 0;
        case Relation::Neq: return sgn(v) != 0;
        case Relation::Gt:  return sgn(v) > 0;
        case Relation::Geq: return sgn(v) >= 0;
        case Relation::Lt:  return sgn(v) < 0;
        case Relation::Leq: return sgn(v) <= 0;
    }
    return false;
}

// A direction is a correct witness iff there is a base at which every
// constraint holds (the subtropical guarantee is asymptotic).
static bool witnessValidatesAtSomeBase(const SubtropicalResult& r,
                                       const std::vector<SubtropicalConstraint>& cs,
                                       const std::vector<VarId>& vars) {
    for (long b : {2L, 4L, 16L, 256L, 65536L, 1L << 24}) {
        auto model = SubtropicalSatFinder::materialize(r.dir, vars, mpq_class(b));
        bool all = true;
        for (const auto& c : cs) {
            if (!relHolds(c.rel, evalPoly(c, model))) { all = false; break; }
        }
        if (all) return true;
    }
    return false;
}

TEST_CASE("subtropical: x*y > 0 needs equal signs") {
    std::vector<SubtropicalConstraint> cs = {{{mono(1, {{X, 1}, {Y, 1}})}, Relation::Gt}};
    std::vector<VarId> vars = {X, Y};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
    // x and y must have the same sign for x*y > 0.
    CHECK(r.dir.signs.at(X) == r.dir.signs.at(Y));
}

TEST_CASE("subtropical: x*y < 0 needs opposite signs") {
    std::vector<SubtropicalConstraint> cs = {{{mono(1, {{X, 1}, {Y, 1}})}, Relation::Lt}};
    std::vector<VarId> vars = {X, Y};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
    CHECK(r.dir.signs.at(X) != r.dir.signs.at(Y));
}

TEST_CASE("subtropical: x^2 - 2 > 0 (dominating square)") {
    // x^2 - 2 > 0 : frame x^2 must dominate the constant; need a_x >= 1.
    std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 2}}), mono(-2, {})}, Relation::Gt}};
    std::vector<VarId> vars = {X};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
}

TEST_CASE("subtropical: conjunction x - y > 0 and y > 0") {
    std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 1}}), mono(-1, {{Y, 1}})}, Relation::Gt},  // x - y > 0
        {{mono(1, {{Y, 1}})}, Relation::Gt}};                     // y > 0
    std::vector<VarId> vars = {X, Y};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
}

TEST_CASE("subtropical: 3-var system with mixed signs") {
    // x*z > 0, y*z < 0, x - y > 0
    std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 1}, {Z, 1}})}, Relation::Gt},
        {{mono(1, {{Y, 1}, {Z, 1}})}, Relation::Lt},
        {{mono(1, {{X, 1}}), mono(-1, {{Y, 1}})}, Relation::Gt}};
    std::vector<VarId> vars = {X, Y, Z};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
}

TEST_CASE("subtropical: bails on equality") {
    std::vector<SubtropicalConstraint> cs = {{{mono(1, {{X, 1}}), mono(-3, {})}, Relation::Eq}};
    std::vector<VarId> vars = {X};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.unsupported);
    CHECK_FALSE(r.found);
}

TEST_CASE("subtropical: does not find x^2 + 1 < 0 (unsat shape)") {
    std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 2}}), mono(1, {})}, Relation::Lt}};
    std::vector<VarId> vars = {X};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK_FALSE(r.found);
}

TEST_CASE("subtropical: x != 0 disequation (no parity constraint)") {
    std::vector<SubtropicalConstraint> cs = {{{mono(1, {{X, 1}})}, Relation::Neq}};
    std::vector<VarId> vars = {X};
    auto r = SubtropicalSatFinder{}.find(cs, vars);
    CHECK(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
}

TEST_CASE("subtropical: materialize builds s * base^a") {
    SubtropicalDirection d;
    d.exponents[X] = mpz_class(2);
    d.signs[X] = -1;
    d.exponents[Y] = mpz_class(-1);
    d.signs[Y] = 1;
    auto m = SubtropicalSatFinder::materialize(d, {X, Y}, mpq_class(3));
    CHECK(m.at(X) == mpq_class(-9));               // -(3^2)
    CHECK(m.at(Y) == mpq_class(1, 3));             // +(3^-1)
}

TEST_CASE("subtropical: shared linear rows withdraw failed frame bounds") {
    // The first frame x needs a_x > a_y and a_x > 0, contradicting 1-x.
    // The sibling frame y works with a_y > 0 > a_x. A failed child must not
    // retain its bounds, and the repeated 1-x row must remain reusable.
    std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 1}}), mono(1, {{Y, 1}}), mono(-1, {})}, Relation::Gt},
        {{mono(1, {}), mono(-1, {{X, 1}})}, Relation::Gt},
        {{mono(1, {{X, 1}})}, Relation::Gt},
        {{mono(1, {{Y, 1}})}, Relation::Gt}};
    SubtropicalSatFinder::Statistics stats;
    const auto r = SubtropicalSatFinder{}.find(cs, {X, Y}, &stats);
    REQUIRE(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, {X, Y}));
    CHECK(stats.contexts == 1);
    CHECK(stats.backtracks > 0);
    CHECK(stats.reusedRows > 0);
    CHECK(stats.parityConflicts > 0);
}

TEST_CASE("subtropical: mixed dense direction rows retain a feasible common ray") {
    std::vector<VarId> vars;
    for (unsigned i = 1; i <= 8; ++i) vars.push_back(VarId{i});
    std::vector<SubtropicalConstraint> cs;
    unsigned state = 947;
    for (unsigned c = 0; c < 8; ++c) {
        SubtropicalConstraint constraint{{}, Relation::Gt};
        std::vector<std::pair<VarId, int>> frame;
        for (auto var : vars) frame.emplace_back(var, 4);
        constraint.monomials.push_back(mono(1, frame));
        for (unsigned j = 0; j < 6; ++j) {
            std::vector<int> exponents(vars.size(), 0);
            for (unsigned degree = 0; degree < 31; ++degree) {
                state = state * 1664525U + 1013904223U;
                ++exponents[(state >> 16) % vars.size()];
            }
            std::vector<std::pair<VarId, int>> powers;
            for (size_t i = 0; i < vars.size(); ++i)
                if (exponents[i]) powers.emplace_back(vars[i], exponents[i]);
            constraint.monomials.push_back(mono(-1, powers));
        }
        cs.push_back(std::move(constraint));
    }
    for (auto var : vars) cs.push_back({{mono(1, {{var, 1}})}, Relation::Gt});
    SubtropicalSatFinder::Statistics stats;
    const auto r = SubtropicalSatFinder{}.find(cs, vars, &stats);
    REQUIRE(r.found);
    CHECK(witnessValidatesAtSomeBase(r, cs, vars));
    CHECK(stats.contexts == 1);
    CHECK_FALSE(stats.exhausted);
}

TEST_CASE("subtropical: shared linear allocation limits leave the decision open") {
    const std::vector<SubtropicalConstraint> cs = {
        {{mono(1, {{X, 2}}), mono(-2, {})}, Relation::Gt}};
    SubtropicalSatFinder::Config cfg;
    cfg.linearRowCap = 0;
    SubtropicalSatFinder::Statistics stats;
    CHECK_FALSE(SubtropicalSatFinder{cfg}.find(cs, {X}, &stats).found);
    CHECK(stats.exhausted);
    CHECK(stats.definitions == 0);
    CHECK(SubtropicalSatFinder{}.find(cs, {X}).found);
}
