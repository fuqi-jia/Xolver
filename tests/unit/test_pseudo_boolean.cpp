#include "search/bitblast/PseudoBooleanEncoder.h"
#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>

using namespace xolver;
using namespace xolver::bitblast;

namespace {
void checkThreshold(const std::vector<long>& weights, const mpz_class& scale = 1) {
    for (long threshold = -6; threshold <= 12; ++threshold) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        std::vector<SatLit> variables;
        for (size_t i = 0; i < weights.size(); ++i) variables.push_back(enc.mkVar(1).bits[0]);
        std::vector<WeightedLiteral> terms;
        for (size_t i = 0; i < weights.size(); ++i)
            terms.push_back({variables[i], scale * weights[i]});
        // Exercise repeated, complementary and constant literals together.
        terms.push_back({variables[0].negated(), scale * 2});
        terms.push_back({variables[0], scale * 3});
        terms.push_back({enc.constTrue(), -scale});
        terms.push_back({enc.constFalse(), scale * 7});
        WorkBudget work;
        PseudoBooleanEncoder pb(enc, work);
        mpz_class bound = scale * threshold;
        if (scale > 1) bound += scale - 1;
        const auto root = pb.lessEqual(terms, bound);
        REQUIRE(root.has_value());
        for (unsigned mask = 0; mask < (1u << weights.size()); ++mask) {
            mpz_class value = -scale;
            std::vector<SatLit> assignments;
            for (size_t i = 0; i < weights.size(); ++i) {
                const bool chosen = mask & (1u << i);
                assignments.push_back(chosen ? variables[i] : variables[i].negated());
                if (chosen) value += scale * weights[i];
            }
            value += scale * ((mask & 1) ? 3 : 2);
            const bool expected = value <= bound;
            assignments.push_back(expected ? *root : root->negated());
            CHECK(sat->solve(assignments) == SatSolver::SolveResult::Sat);
            assignments.back() = assignments.back().negated();
            CHECK(sat->solve(assignments) == SatSolver::SolveResult::Unsat);
        }
    }
}

struct BinaryFixture {
    NativeTerms ir;
    BinaryFixture() {
        ir.registerSort(0, SortKind::Bool);
        ir.registerSort(1, SortKind::Int);
        ir.setBoolSortId(0);
        ir.setIntSortId(1);
    }
    ExprId integer(const mpz_class& value) { return ir.add({Kind::ConstInt, 1, {}, Payload(value.get_str())}); }
    ExprId variable(const char* name) { return ir.add({Kind::Variable, 1, {}, Payload(std::string(name))}); }
    ExprId term(Kind kind, std::vector<ExprId> children) {
        const bool arithmetic = kind == Kind::Add || kind == Kind::Mul || kind == Kind::Sub || kind == Kind::Neg;
        TermExpr expression{kind, arithmetic ? SortId(1) : SortId(0), {}, {}};
        for (const auto child : children) expression.children.push_back(child);
        return ir.add(std::move(expression));
    }
    void bounds(ExprId variable, std::vector<ExprId>& roots) {
        roots.push_back(term(Kind::Geq, {variable, integer(0)}));
        roots.push_back(term(Kind::Leq, {variable, integer(1)}));
    }
};
}

TEST_CASE("PseudoBooleanEncoder: reified signed thresholds match exhaustive assignments") {
    checkThreshold({3, -2, 5, 0});
    checkThreshold({-4, 2, -1, 3}, mpz_class(1) << 100);
}

TEST_CASE("PseudoBooleanEncoder: long thresholds use an explicit stack") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    std::vector<WeightedLiteral> terms;
    for (int i = 0; i < 5000; ++i) terms.push_back({enc.mkVar(1).bits[0], 1});
    WorkBudget work(100000);
    PseudoBooleanEncoder pb(enc, work);
    const auto root = pb.lessEqual(terms, 0);
    REQUIRE(root.has_value());
    enc.assertLit(*root);
    CHECK(sat->solve() == SatSolver::SolveResult::Sat);
    for (const auto& term : terms) CHECK_FALSE(litValue(*sat, term.literal));
}

TEST_CASE("PseudoBooleanEncoder: partial resource-limited encodings expose no literal") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    std::vector<WeightedLiteral> terms;
    for (int i = 0; i < 20; ++i) terms.push_back({enc.mkVar(1).bits[0], i + 1});
    WorkBudget work(100);
    PseudoBooleanEncoder pb(enc, work);
    CHECK_FALSE(pb.lessEqual(terms, 105).has_value());
    WorkBudget available;
    enc.setVarBudget(enc.varCount());
    PseudoBooleanEncoder capped(enc, available);
    CHECK_FALSE(capped.lessEqual(terms, 105).has_value());
    CHECK(enc.overflowed());
}

TEST_CASE("Binary integer portfolio: signed strict bounds and Boolean contexts validate exactly") {
    for (auto relation : {Kind::Eq, Kind::Distinct, Kind::Lt, Kind::Leq, Kind::Gt, Kind::Geq}) {
        BinaryFixture f;
        const auto x = f.variable("x"), y = f.variable("y");
        std::vector<ExprId> roots;
        // -3*x < 1 and 2*x < 3 imply 0 <= x <= 1 after integer rounding.
        roots.push_back(f.term(Kind::Lt, {f.term(Kind::Mul, {f.integer(-3), x}), f.integer(1)}));
        roots.push_back(f.term(Kind::Lt, {f.term(Kind::Mul, {f.integer(2), x}), f.integer(3)}));
        f.bounds(y, roots);
        const mpz_class weight = mpz_class(1) << 100;
        const auto sum = f.term(Kind::Add, {f.term(Kind::Mul, {f.integer(weight), x}),
            f.term(Kind::Mul, {f.integer(-weight), y})});
        const auto predicate = f.term(relation, {sum, f.integer(0)});
        const auto impossible = f.term(Kind::Gt, {sum, f.integer(weight)});
        roots.push_back(f.term(Kind::Not, {impossible}));
        roots.push_back(f.term(Kind::Or, {predicate,
            f.term(Kind::Not, {predicate})}));
        // Force nontrivial use of the reified relation and its negation.
        const bool requireTrue = relation == Kind::Eq || relation == Kind::Leq || relation == Kind::Geq;
        roots.push_back(requireTrue ? predicate : f.term(Kind::Not, {predicate}));
        EagerBitBlastSolver solver;
        solver.setFarkasBudget(33, 1000);
        const auto result = solver.solveBinary(f.ir, roots);
        REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
        const mpz_class value = weight * (result.model.at("x") - result.model.at("y"));
        bool holds = false;
        switch (relation) {
            case Kind::Eq: holds = value == 0; break;
            case Kind::Distinct: holds = value != 0; break;
            case Kind::Lt: holds = value < 0; break;
            case Kind::Leq: holds = value <= 0; break;
            case Kind::Gt: holds = value > 0; break;
            case Kind::Geq: holds = value >= 0; break;
            default: break;
        }
        CHECK(holds == requireTrue);
        CHECK(value <= weight);
    }
}

TEST_CASE("Binary integer portfolio: branch-local bounds do not qualify an unbounded variable") {
    BinaryFixture f;
    const auto x = f.variable("x");
    const auto zero = f.term(Kind::Eq, {x, f.integer(0)});
    const auto two = f.term(Kind::Eq, {x, f.integer(2)});
    EagerBitBlastSolver solver;
    const auto result = solver.solveBinary(f.ir, {f.term(Kind::Or, {zero, two})});
    CHECK(result.status == EagerBitBlastSolver::Status::Unknown);
    const auto qualified = solver.solveBinary(f.ir, {zero});
    REQUIRE(qualified.status == EagerBitBlastSolver::Status::Sat);
    CHECK(qualified.model.at("x") == 0);
    CHECK(solver.solveBinary(f.ir, {two}).status == EagerBitBlastSolver::Status::Unknown);
}

TEST_CASE("Binary polynomial encoding: positive powers collapse without losing exact models") {
    BinaryFixture f;
    const auto x = f.variable("x"), y = f.variable("y");
    std::vector<ExprId> roots;
    f.bounds(x, roots);
    f.bounds(y, roots);
    roots.push_back(f.term(Kind::Eq, {f.term(Kind::Mul, {x, x, y}), f.integer(1)}));
    EagerBitBlastSolver solver;
    const auto result = solver.solve(f.ir, roots);
    REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == 1);
    CHECK(result.model.at("y") == 1);
}
