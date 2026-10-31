#include <doctest/doctest.h>
#include "search/refute/PolynomialResidueRefutation.h"
#include "search/refute/PolynomialBooleanRefutation.h"
#include <algorithm>
#include <xolver/Solver.h>

using namespace xolver;

namespace {
RationalPolynomial variable(VarId id) { return RationalPolynomial::fromVar(id, 1, 1); }
RationalPolynomial constant(const mpq_class& value) { return RationalPolynomial::fromConstant(value); }
PolynomialResidueLimits allocation() {
    PolynomialResidueLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
    return limits;
}
}

TEST_CASE("Polynomial residues: coupled equalities drop quotient variables before enumeration") {
    const auto x = variable(0), y = variable(1), z = variable(2), w = variable(3);
    std::vector<SignRefuteConstraint> constraints{
        {x*x + y*y - constant(3)*z, Relation::Eq, SatLit::positive(1)},
        {x + y - constant(1) - constant(3)*w, Relation::Eq, SatLit::negative(2)}};
    // Unrelated integer definitions must not trigger a global variable cap or
    // contribute premises to a conflict in the two-variable residue component.
    for (VarId id = 4; id < 36; ++id)
        constraints.push_back({variable(id), Relation::Eq, SatLit::positive(id + 1)});
    PolynomialResidueStatistics stats;
    auto conflict = refuteByPolynomialResidues(constraints, allocation(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::positive(1)) != conflict->end());
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::negative(2)) != conflict->end());
    CHECK(stats.assignments < 100);
    CHECK(stats.moduli == 2);
    CHECK_FALSE(stats.exhausted);
}

TEST_CASE("Polynomial residues: rational content and composite moduli preserve integer roots") {
    const auto x = variable(0);
    CHECK(refuteByPolynomialResidues({{x - constant(mpq_class(1,2)), Relation::Eq,
        SatLit::positive(1)}}, allocation()).has_value());
    CHECK_FALSE(refuteByPolynomialResidues({{constant(mpq_class(2,3))*x - constant(mpq_class(4,3)),
        Relation::Eq, SatLit::positive(1)}}, allocation()));
    auto limits = allocation();
    limits.moduli = {4};
    CHECK(refuteByPolynomialResidues({{x*x - constant(2), Relation::Eq,
        SatLit::positive(1)}}, limits).has_value());
    CHECK_FALSE(refuteByPolynomialResidues({{x*x - constant(1), Relation::Eq,
        SatLit::positive(1)}}, limits));
    // Congruence of a nonzero integer to zero cannot refute a disequality.
    CHECK_FALSE(refuteByPolynomialResidues({{constant(4), Relation::Neq,
        SatLit::positive(1)}}, limits));
    CHECK_FALSE(refuteByPolynomialResidues({{x*x - constant(2), Relation::Gt,
        SatLit::positive(1)}}, limits));
}

TEST_CASE("Polynomial residues: known integer witnesses survive every supported modulus") {
    const auto x = variable(0), y = variable(1);
    for (int a = -3; a <= 3; ++a) for (int b = -3; b <= 3; ++b) {
        const auto p = (x - constant(a)) * (y - constant(b));
        const auto q = x*x + y*y - constant(a*a + b*b);
        CHECK_FALSE(refuteByPolynomialResidues({
            {p, Relation::Eq, SatLit::positive(1)},
            {q, Relation::Eq, SatLit::positive(2)}}, allocation()));
    }
}

TEST_CASE("Polynomial residues: expired and insufficient allocations leave the obligation open") {
    const auto x = variable(0), y = variable(1);
    const std::vector<SignRefuteConstraint> constraints{
        {x*x + y*y - constant(3), Relation::Eq, SatLit::positive(1)}};
    auto limits = allocation();
    limits.moduli = {4};
    limits.assignments = 1;
    PolynomialResidueStatistics stats;
    CHECK_FALSE(refuteByPolynomialResidues(constraints, limits, &stats));
    CHECK(stats.exhausted);
    limits = allocation();
    limits.deadline = std::chrono::steady_clock::now();
    CHECK_FALSE(refuteByPolynomialResidues(constraints, limits, &stats));
    CHECK(stats.exhausted);
    limits = allocation();
    limits.work = 1;
    CHECK_FALSE(refuteByPolynomialResidues(constraints, limits, &stats));
    CHECK(stats.exhausted);
    limits = allocation();
    limits.moduli = {0, 1, -3, 65536};
    CHECK_FALSE(refuteByPolynomialResidues(constraints, limits));
}

TEST_CASE("Polynomial Boolean residues: integer conflicts do not refute a real relaxation") {
    for (auto kind : {SortKind::Int, SortKind::Real}) {
        NativeTerms terms;
        terms.registerSort(0, kind);
        terms.registerSort(1, SortKind::Bool);
        terms.setBoolSortId(1);
        auto op = [&](Kind k, std::initializer_list<ExprId> children, SortId sort) {
            TermExpr node{k, sort, {}, {}};
            for (auto child : children) node.children.push_back(child);
            return terms.add(std::move(node));
        };
        auto numeral = [&](int64_t n) { return terms.add({Kind::ConstInt, 0, {}, Payload(n)}); };
        auto var = [&](const char* name) { return terms.add({Kind::Variable, 0, {}, Payload(std::string(name))}); };
        const auto x = var("x"), y = var("y"), z = var("z"), w = var("w");
        const auto three = numeral(3);
        const std::vector<ExprId> roots{
            op(Kind::Eq, {op(Kind::Add, {op(Kind::Mul, {x,x}, 0), op(Kind::Mul, {y,y}, 0)}, 0),
                op(Kind::Mul, {three,z}, 0)}, 1),
            op(Kind::Eq, {op(Kind::Add, {x,y}, 0),
                op(Kind::Add, {numeral(1),op(Kind::Mul, {three,w}, 0)}, 0)}, 1)};
        BooleanRefutationLimits limits;
        limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
        PolynomialBooleanStatistics stats;
        CHECK(refutePolynomialBoolean(terms, roots, limits, &stats) == (kind == SortKind::Int));
        CHECK(stats.residueCalls == (kind == SortKind::Int ? 1 : 0));
        // An alternative with an integer witness remains open.
        auto alternative = op(Kind::Eq, {x,numeral(0)}, 1);
        auto disjunction = op(Kind::Or, {roots[1],alternative}, 1);
        CHECK_FALSE(refutePolynomialBoolean(terms, {roots[0],disjunction}, limits));
    }
}

TEST_CASE("Polynomial residues: Boolean explanations withdraw with assumptions and scopes") {
    Solver solver;
    solver.setLogic("QF_NIA");
    auto op = [&](Kind kind, std::vector<Term> children) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
    };
    const auto x = solver.mkConst(solver.intSort(), "x");
    const auto y = solver.mkConst(solver.intSort(), "y");
    const auto z = solver.mkConst(solver.intSort(), "z");
    const auto w = solver.mkConst(solver.intSort(), "w");
    const auto p = solver.mkConst(solver.boolSort(), "p");
    const auto notP = op(Kind::Not, {p});
    const auto three = solver.mkInt(3);
    solver.assertFormula(op(Kind::Eq, {op(Kind::Add, {
        op(Kind::Mul, {x,x}), op(Kind::Mul, {y,y})}), op(Kind::Mul, {three,z})}));
    solver.assertFormula(op(Kind::Implies, {p, op(Kind::Eq, {
        op(Kind::Add, {x,y}), op(Kind::Add, {solver.mkInt(1),op(Kind::Mul, {three,w})})})}));
    for (int repeat = 0; repeat < 2; ++repeat) {
        REQUIRE((solver.checkSatAssuming({p}) == Result::Unsat));
        const auto core = solver.getUnsatCore();
        CHECK(std::find(core.begin(), core.end(), p) != core.end());
        REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        solver.push();
        solver.assertFormula(p);
        REQUIRE((solver.checkSat() == Result::Unsat));
        solver.pop();
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    }
}
