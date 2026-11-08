#include <doctest/doctest.h>
#include "search/arith/LinearDifferenceEqualityIndex.h"
#include "xolver/Solver.h"
#include <filesystem>
#include <fstream>

using namespace xolver;

namespace {
LinearAtomPayload difference(std::string a, std::string b, mpq_class coefficient,
                             Relation relation, mpq_class rhs = 0) {
    return {LinearFormKey{{{std::move(a), coefficient}, {std::move(b), -coefficient}}},
            relation, RealValue::fromMpq(std::move(rhs))};
}

bool holds(Relation relation, const mpq_class& lhs, const mpq_class& rhs) {
    switch (relation) {
        case Relation::Eq: return lhs == rhs;
        case Relation::Neq: return lhs != rhs;
        case Relation::Lt: return lhs < rhs;
        case Relation::Leq: return lhs <= rhs;
        case Relation::Gt: return lhs > rhs;
        case Relation::Geq: return lhs >= rhs;
    }
    return false;
}
} // namespace

TEST_CASE("Linear difference equalities: sparse pairs retain aliases and shared order") {
    std::vector<std::string> names{"z", "a", "", "m", "a"};
    for (int i = 0; i < 512; ++i) names.push_back("unrelated-" + std::to_string(i));
    LinearDifferenceEqualityIndex index;
    index.add(difference("z", "a", 1, Relation::Leq), true, {1, true});
    index.add(difference("a", "z", 1, Relation::Leq), true, {2, true});
    index.add(difference("m", "a", 1, Relation::Eq), true, {3, true});
    index.add(difference("z", "m", 1, Relation::Eq, 5), true, {4, true});
    index.add(difference("a", "absent", 1, Relation::Eq), true, {5, true});
    const auto pairs = index.pinnedPairs(names);
    REQUIRE(pairs.size() == 4);
    const std::vector<std::pair<size_t, size_t>> expected{{0, 1}, {0, 4}, {1, 3}, {3, 4}};
    for (size_t i = 0; i < pairs.size(); ++i) {
        CHECK(pairs[i].first == expected[i].first);
        CHECK(pairs[i].second == expected[i].second);
        CHECK(pairs[i].lowerReason == SatLit(i < 2 ? 1 : 3, true));
        CHECK(pairs[i].upperReason == SatLit(i < 2 ? 2 : 3, true));
    }
}

TEST_CASE("Linear difference equalities: exact signed scales and negative literals") {
    const std::vector<std::string> names{"a", "z"};
    for (const mpq_class scale : {mpq_class(1, 3), mpq_class(-7, 11),
            mpq_class("1361129467683753853853498429727072845824/17")}) {
        LinearDifferenceEqualityIndex index;
        index.add(difference("z", "a", scale, Relation::Gt), false, {1, false});
        index.add(difference("z", "a", scale, Relation::Lt), false, {2, false});
        const auto pairs = index.pinnedPairs(names);
        REQUIRE(pairs.size() == 1);
        CHECK(pairs[0].lowerReason == SatLit(scale > 0 ? 1 : 2, false));
        CHECK(pairs[0].upperReason == SatLit(scale > 0 ? 2 : 1, false));
    }
}

TEST_CASE("Linear difference equalities: incomplete bounds do not assert equality") {
    const std::vector<std::string> names{"x", "y"};
    LinearDifferenceEqualityIndex index;
    index.add(difference("x", "y", 1, Relation::Lt), true, {1, true});
    index.add(difference("x", "y", 1, Relation::Gt), true, {2, true});
    index.add(difference("x", "y", 1, Relation::Eq), false, {3, false});
    CHECK(index.pinnedPairs(names).empty());
    index.add(difference("x", "y", 1, Relation::Geq, -1), true, {4, true});
    index.add(difference("x", "y", 1, Relation::Leq, 1), true, {5, true});
    CHECK(index.pinnedPairs(names).empty());

    LinearDifferenceEqualityIndex offset;
    offset.add(difference("x", "y", 1, Relation::Eq, 1), true, {6, true});
    CHECK(offset.pinnedPairs(names).empty());
    LinearDifferenceEqualityIndex unequalCoefficients;
    auto atom = difference("x", "y", 1, Relation::Eq);
    atom.lhs.terms[1].second = -2;
    unequalCoefficients.add(atom, true, {7, true});
    CHECK(unequalCoefficients.pinnedPairs(names).empty());
}

TEST_CASE("Linear difference equalities: explanations independently exclude unequal witnesses") {
    const std::vector<std::string> names{"x", "y"};
    for (Relation first : {Relation::Eq, Relation::Neq, Relation::Lt,
                           Relation::Leq, Relation::Gt, Relation::Geq}) {
        for (Relation second : {Relation::Eq, Relation::Neq, Relation::Lt,
                                Relation::Leq, Relation::Gt, Relation::Geq}) {
            for (bool value : {false, true}) {
                const auto a = difference("x", "y", mpq_class(-3, 7), first);
                const auto b = difference("y", "x", mpq_class(5, 11), second);
                LinearDifferenceEqualityIndex index;
                index.add(a, value, {1, value});
                index.add(b, true, {2, true});
                for (const auto& pair : index.pinnedPairs(names)) {
                    CHECK(pair.first == 0);
                    CHECK(pair.second == 1);
                    bool equalWitness = false;
                    for (int xi = -4; xi <= 4; ++xi) {
                        for (int yi = -4; yi <= 4; ++yi) {
                            const mpq_class x(xi, 2), y(yi, 2);
                            bool premises = true;
                            for (SatLit reason : {pair.lowerReason, pair.upperReason}) {
                                REQUIRE((reason.var == 1 || reason.var == 2));
                                const auto& atom = reason.var == 1 ? a : b;
                                const mpq_class lhs = reason.var == 1
                                    ? mpq_class(-3, 7) * (x - y) : mpq_class(5, 11) * (y - x);
                                premises &= holds(atom.rel, lhs, atom.rhs.asRational()) == reason.sign;
                            }
                            if (premises) {
                                CHECK(x == y);
                                equalWitness = true;
                            }
                        }
                    }
                    CHECK(equalWitness);
                }
            }
        }
    }
}

TEST_CASE("Linear difference equalities: integer and real UF scopes withdraw explanations") {
    for (const std::string domain : {"Int", "Real"}) {
        const auto path = std::filesystem::temp_directory_path() /
            ("xolver_difference_scope_" + domain + ".smt2");
        std::ofstream(path) << "(set-logic QF_UFL" << (domain == "Int" ? "IA" : "RA") << ")\n"
            << "(declare-const z " << domain << ")(declare-const a " << domain << ")\n"
            << "(declare-fun f (" << domain << ") " << domain << ")\n"
            << "(assert (distinct (f z) (f a)))(assert (<= z a))(check-sat)\n";
        Solver solver;
        REQUIRE(solver.parseFile(path.string()));
        std::filesystem::remove(path);
        const auto sort = domain == "Int" ? solver.intSort() : solver.realSort();
        const auto z = solver.mkConst(sort, "z"), a = solver.mkConst(sort, "a");
        const auto reverse = solver.mkOp(static_cast<uint32_t>(Kind::Geq), {z, a});
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        solver.push();
        solver.assertFormula(reverse);
        CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
        solver.pop();
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        CHECK(static_cast<int>(solver.checkSatAssuming({reverse})) == static_cast<int>(Result::Unsat));
        REQUIRE(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    }
}
