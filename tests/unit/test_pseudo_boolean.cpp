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

TEST_CASE("PseudoBooleanEncoder: arithmetic fallback preserves every reified weighted assignment") {
    auto sat=createSatSolver();
    BitBlastEncoder enc(*sat);
    enc.setVarBudget(20000);
    std::vector<WeightedLiteral> terms;
    mpz_class total=0;
    uint32_t state=0x9e3779b9u;
    for (int i=0;i<14;++i) {
        state^=state<<13;state^=state>>17;state^=state<<5;
        mpz_class weight=4194304u+(state&0x3fffffu);
        terms.push_back({enc.mkVar(1).bits[0],weight});
        total+=weight;
    }
    const mpz_class bound=total/2+17;
    WorkBudget work;
    PseudoBooleanEncoder pb(enc,work);
    const auto root=pb.lessEqual(terms,bound);
    REQUIRE(root);
    REQUIRE(pb.statistics().carrySaveThresholds>0);
    CHECK(pb.statistics().compressors>0);
    CHECK(enc.varCount()<10000);
    std::vector<SatLit> assignments;
    assignments.reserve(terms.size()+1);
    for (unsigned mask=0;mask<(1u<<terms.size());++mask) {
        mpz_class value=0;
        assignments.clear();
        for (size_t i=0;i<terms.size();++i) {
            const bool chosen=mask&(1u<<i);
            assignments.push_back(chosen?terms[i].literal:terms[i].literal.negated());
            if (chosen) value+=terms[i].weight;
        }
        const bool expected=value<=bound;
        assignments.push_back(expected?*root:root->negated());
        CHECK(sat->solve(assignments)==SatSolver::SolveResult::Sat);
        assignments.back()=assignments.back().negated();
        CHECK(sat->solve(assignments)==SatSolver::SolveResult::Unsat);
    }
}

TEST_CASE("Finite integer portfolio: signed strict bounds and Boolean contexts validate exactly") {
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
        const auto result = solver.solveLinear(f.ir, roots);
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

TEST_CASE("Finite integer portfolio: branch-local bounds do not qualify an unbounded variable") {
    BinaryFixture f;
    const auto x = f.variable("x");
    const auto zero = f.term(Kind::Eq, {x, f.integer(0)});
    const auto two = f.term(Kind::Eq, {x, f.integer(2)});
    EagerBitBlastSolver solver;
    const auto result = solver.solveLinear(f.ir, {f.term(Kind::Or, {zero, two})});
    CHECK(result.status == EagerBitBlastSolver::Status::Unknown);
    const auto qualified = solver.solveLinear(f.ir, {zero});
    REQUIRE(qualified.status == EagerBitBlastSolver::Status::Sat);
    CHECK(qualified.model.at("x") == 0);
    const auto nonbinary = solver.solveLinear(f.ir, {two});
    REQUIRE(nonbinary.status == EagerBitBlastSolver::Status::Sat);
    CHECK(nonbinary.model.at("x") == 2);
    CHECK(solver.solveLinear(f.ir, {f.term(Kind::Or, {zero, two})}).status == EagerBitBlastSolver::Status::Unknown);
}

TEST_CASE("Finite integer portfolio: signed wide weights preserve exact Boolean branch models") {
    BinaryFixture f;
    const auto x=f.variable("x"),y=f.variable("y");
    const auto choose=f.ir.add({Kind::Variable,0,{},Payload(std::string("choose"))});
    std::vector<ExprId> roots{
        f.term(Kind::Geq,{x,f.integer(-5)}),f.term(Kind::Leq,{x,f.integer(3)}),
        f.term(Kind::Geq,{y,f.integer(2)}),f.term(Kind::Leq,{y,f.integer(8)})};
    const mpz_class weight=mpz_class(1)<<100;
    const auto sum=f.term(Kind::Add,{f.term(Kind::Mul,{f.integer(weight),x}),
        f.term(Kind::Mul,{f.integer(mpz_class(-weight-1)),y})});
    const auto target=f.term(Kind::Eq,{sum,f.integer(mpz_class(-5*weight-3))});
    const auto impossible=f.term(Kind::Gt,{y,f.integer(100)});
    roots.push_back(f.term(Kind::Or,{f.term(Kind::And,{choose,target}),
        f.term(Kind::And,{f.term(Kind::Not,{choose}),impossible})}));
    EagerBitBlastSolver solver;
    solver.setFarkasBudget(33,1000);
    const auto result=solver.solveLinear(f.ir,roots);
    REQUIRE(result.status==EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x")==-2);
    CHECK(result.model.at("y")==3);
    CHECK(result.boolModel.at("choose"));
    CHECK(weight*result.model.at("x")-(weight+1)*result.model.at("y")==-5*weight-3);
}

TEST_CASE("Finite integer portfolio: root equality propagation qualifies bounded aliases") {
    BinaryFixture f;
    const auto x=f.variable("x"),y=f.variable("y");
    std::vector<ExprId> roots{
        f.term(Kind::Geq,{x,f.integer(1)}),f.term(Kind::Leq,{x,f.integer(4)}),
        f.term(Kind::Eq,{y,f.term(Kind::Add,{f.term(Kind::Mul,{f.integer(3),x}),f.integer(2)})}),
        f.term(Kind::Distinct,{y,f.integer(8)})};
    EagerBitBlastSolver solver;
    const auto result=solver.solveLinear(f.ir,roots);
    REQUIRE(result.status==EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x")>=1);CHECK(result.model.at("x")<=4);
    CHECK(result.model.at("y")==3*result.model.at("x")+2);
    CHECK(result.model.at("y")!=8);
}

TEST_CASE("Finite integer portfolio: all signed relations retain their truth under negation") {
    for (auto relation : {Kind::Eq,Kind::Distinct,Kind::Lt,Kind::Leq,Kind::Gt,Kind::Geq}) {
        BinaryFixture f;
        const auto x=f.variable("x");
        std::vector<ExprId> roots{
            f.term(Kind::Geq,{x,f.integer(-8)}),f.term(Kind::Leq,{x,f.integer(-2)})};
        const auto predicate=f.term(relation,{x,f.integer(-5)});
        roots.push_back(f.term(Kind::Not,{predicate}));
        EagerBitBlastSolver solver;
        const auto result=solver.solveLinear(f.ir,roots);
        REQUIRE(result.status==EagerBitBlastSolver::Status::Sat);
        const auto& value=result.model.at("x");
        CHECK(value>=-8);CHECK(value<=-2);
        switch (relation) {
            case Kind::Eq: CHECK(value!=-5);break;
            case Kind::Distinct: CHECK(value==-5);break;
            case Kind::Lt: CHECK(value>=-5);break;
            case Kind::Leq: CHECK(value>-5);break;
            case Kind::Gt: CHECK(value<=-5);break;
            case Kind::Geq: CHECK(value<-5);break;
            default: break;
        }
    }
}

TEST_CASE("Finite integer portfolio: incomplete domains and nonlinear formulas fall through") {
    BinaryFixture f;
    const auto x=f.variable("x"),y=f.variable("y");
    std::vector<ExprId> roots;
    f.bounds(x,roots);
    EagerBitBlastSolver solver;
    roots.push_back(f.term(Kind::Gt,{y,f.integer(0)}));
    CHECK(solver.solveLinear(f.ir,roots).status==EagerBitBlastSolver::Status::Unknown);
    f.bounds(y,roots);
    roots.push_back(f.term(Kind::Eq,{f.term(Kind::Mul,{x,y}),f.integer(1)}));
    CHECK(solver.solveLinear(f.ir,roots).status==EagerBitBlastSolver::Status::Unknown);
    const auto nonlinear=solver.solve(f.ir,roots);
    REQUIRE(nonlinear.status==EagerBitBlastSolver::Status::Sat);
    CHECK(nonlinear.model.at("x")==1);CHECK(nonlinear.model.at("y")==1);
}

TEST_CASE("Finite integer portfolio: a finite refutation yields to the complete theory solver") {
    BinaryFixture f;
    const auto x=f.variable("x");
    const std::vector<ExprId> roots{
        f.term(Kind::Geq,{x,f.integer(-3)}),f.term(Kind::Leq,{x,f.integer(3)}),
        f.term(Kind::Eq,{f.term(Kind::Mul,{f.integer(2),x}),f.integer(1)})};
    EagerBitBlastSolver solver;
    CHECK(solver.solveLinear(f.ir,roots).status==EagerBitBlastSolver::Status::Unknown);
}

TEST_CASE("Finite integer radix encoding: signed offsets and quotient orientation remain exact") {
    for (bool negate : {false,true}) for (int offset : {-17,0,19}) {
        BinaryFixture f;
        const auto word=f.variable("word"),q=f.variable("q"),r=f.variable("r");
        const auto equation=f.term(Kind::Eq,{
            f.term(Kind::Add,{word,f.integer(offset)}),
            f.term(Kind::Add,{f.term(Kind::Mul,{f.integer(negate?-8:8),q}),r})});
        const std::vector<ExprId> roots{
            f.term(Kind::Geq,{word,f.integer(-16-offset)}),f.term(Kind::Leq,{word,f.integer(15-offset)}),
            f.term(Kind::Geq,{q,f.integer(negate?-1:-2)}),f.term(Kind::Leq,{q,f.integer(negate?2:1)}),
            f.term(Kind::Geq,{r,f.integer(0)}),f.term(Kind::Leq,{r,f.integer(7)}),equation,
            f.term(Kind::Not,{f.term(Kind::Distinct,{word,f.integer(-1-offset)})})};
        EagerBitBlastSolver solver;
        const auto result=solver.solveLinear(f.ir,roots);
        REQUIRE(result.status==EagerBitBlastSolver::Status::Sat);
        CHECK(result.model.at("word")==-1-offset);
        CHECK(result.model.at("q")== (negate?1:-1));CHECK(result.model.at("r")==7);
        CHECK(result.model.at("word")+offset==(negate?-8:8)*result.model.at("q")+result.model.at("r"));
    }
}

TEST_CASE("Finite integer radix encoding: nested and repeated definitions retain every equality") {
    BinaryFixture f;
    const auto x=f.variable("x"),a=f.variable("a"),b=f.variable("b"),c=f.variable("c"),
               d=f.variable("d"),e=f.variable("e"),r=f.variable("r");
    std::vector<ExprId> roots;
    for (auto [variable,upper] : std::vector<std::pair<ExprId,int>>{{x,63},{a,3},{b,15},{c,3},{d,3},{e,15},{r,3}}) {
        roots.push_back(f.term(Kind::Geq,{variable,f.integer(0)}));
        roots.push_back(f.term(Kind::Leq,{variable,f.integer(upper)}));
    }
    auto define=[&](ExprId value,int scale,ExprId high,ExprId low) {
        roots.push_back(f.term(Kind::Eq,{value,f.term(Kind::Add,{f.term(Kind::Mul,{f.integer(scale),high}),low})}));
    };
    define(x,16,a,b);define(b,4,c,d);define(x,4,e,r);
    roots.push_back(f.term(Kind::Not,{f.term(Kind::Distinct,{x,f.integer(42)})}));
    EagerBitBlastSolver solver;
    const auto result=solver.solveLinear(f.ir,roots);
    REQUIRE(result.status==EagerBitBlastSolver::Status::Sat);
    const auto& p=result.model;
    CHECK(p.at("x")==42);CHECK(p.at("x")==16*p.at("a")+p.at("b"));
    CHECK(p.at("b")==4*p.at("c")+p.at("d"));CHECK(p.at("x")==4*p.at("e")+p.at("r"));
}

TEST_CASE("Finite integer radix encoding: conditional definitions and later calls do not become root facts") {
    BinaryFixture f;
    const auto x=f.variable("x"),q=f.variable("q"),r=f.variable("r");
    const auto definition=f.term(Kind::Eq,{x,f.term(Kind::Add,{f.term(Kind::Mul,{f.integer(8),q}),r})});
    const std::vector<ExprId> roots{
        f.term(Kind::Eq,{x,f.integer(1)}),f.term(Kind::Eq,{q,f.integer(0)}),
        f.term(Kind::Eq,{r,f.integer(0)}),
        f.term(Kind::Or,{definition,f.term(Kind::Eq,{x,f.integer(1)})})};
    EagerBitBlastSolver solver;
    const auto conditional=solver.solveLinear(f.ir,roots);
    REQUIRE(conditional.status==EagerBitBlastSolver::Status::Sat);
    CHECK(conditional.model.at("x")==1);CHECK(conditional.model.at("q")==0);
    const auto first=solver.solveLinear(f.ir,{definition,f.term(Kind::Eq,{q,f.integer(0)}),f.term(Kind::Eq,{r,f.integer(0)})});
    REQUIRE(first.status==EagerBitBlastSolver::Status::Sat);CHECK(first.model.at("x")==0);
    const auto restored=solver.solveLinear(f.ir,roots);
    REQUIRE(restored.status==EagerBitBlastSolver::Status::Sat);CHECK(restored.model.at("x")==1);
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
