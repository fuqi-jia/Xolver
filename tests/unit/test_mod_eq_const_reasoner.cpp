#include <doctest/doctest.h>

#include "expr/ir.h"
#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/reasoners/ModEqConstFact.h"
#include "theory/arith/nia/reasoners/ModEqConstReasoner.h"
#include "theory/arith/poly/PolynomialKernel.h"

namespace xolver {
namespace {

// Build a Variable expression by name in `ir` with the given sort.
ExprId mkVarExpr(CoreIr& ir, const std::string& name, SortId sort) {
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = sort;
    e.payload = Payload(name);
    return ir.addShared(std::move(e));
}

// A small fixture: integer sort + two variables x, y.
struct Fixture {
    CoreIr ir;
    SortId intSort;
    ExprId xExpr;
    ExprId yExpr;
    ExprId xyAtomExpr;  // a dummy atom ExprId (just a fresh variable expr)
    std::unique_ptr<PolynomialKernel> kernel;

    Fixture() {
        // CoreIr does not own a sort table; SortId is opaque. For tests we
        // pick an arbitrary non-null SortId and register it as the Int sort
        // (the reasoner doesn't inspect sort values, only Kind::Variable).
        intSort = static_cast<SortId>(1);
        ir.setIntSortId(intSort);
        xExpr = mkVarExpr(ir, "x", intSort);
        yExpr = mkVarExpr(ir, "y", intSort);
        xyAtomExpr = mkVarExpr(ir, "__atom_mod_x_y", intSort);
        kernel = createPolynomialKernel();
    }
};

SatLit makeLit(int var, bool sign = false) {
    return SatLit{static_cast<SatVar>(var), sign};
}

}  // namespace

TEST_CASE("ModEqConstReasoner: Rule 2 narrows lower bound (y>=1 → y>=c+1)") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);  // dummy assertion lit

    ModEqConstFactList facts{fact};

    DomainStore domains;
    domains.addLowerBound("y", 1, makeLit(101));

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::DomainUpdated);

    const auto* d = domains.getDomain("y");
    REQUIRE(d != nullptr);
    CHECK(d->hasLower);
    CHECK(d->lower.value == mpz_class(6));  // c+1 = 5+1 = 6
}

TEST_CASE("ModEqConstReasoner: Rule 2 conflict when upper < c+1") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};

    DomainStore domains;
    domains.addLowerBound("y", 1, makeLit(101));
    domains.addUpperBound("y", 3, makeLit(102));  // y<=3 < c+1=6 → conflict

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::Conflict);
    REQUIRE(result.conflict.has_value());
    // Conflict clause must include the fact's reason literal.
    bool foundFactLit = false;
    for (auto l : result.conflict->clause) {
        if (l.var == 100) foundFactLit = true;
    }
    CHECK(foundFactLit);
}

TEST_CASE("ModEqConstReasoner: Rule 3 narrows upper bound (y<=-1 → y<=-c-1)") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};

    DomainStore domains;
    domains.addUpperBound("y", -1, makeLit(101));

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::DomainUpdated);

    const auto* d = domains.getDomain("y");
    REQUIRE(d != nullptr);
    CHECK(d->hasUpper);
    CHECK(d->upper.value == mpz_class(-6));  // -c-1 = -5-1 = -6
}

TEST_CASE("ModEqConstReasoner: Rule 3 conflict when lower > -c-1") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};

    DomainStore domains;
    domains.addLowerBound("y", -3, makeLit(101));  // y >= -3 > -c-1=-6 → conflict
    domains.addUpperBound("y", -1, makeLit(102));

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("ModEqConstReasoner: Rule 1 conflict when c<0 and y non-zero") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = -3;  // negative — only y=0 (EUF mod0) branch could satisfy
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};

    DomainStore domains;
    domains.addLowerBound("y", 1, makeLit(101));  // y >= 1 → y != 0

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::Conflict);
}

TEST_CASE("ModEqConstReasoner: NoChange when y sign unknown") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = fx.yExpr;
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};

    DomainStore domains;
    // No bounds at all — sign unknown, no rule applies.
    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ModEqConstReasoner: NoChange when y is not a Variable") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);

    // Build an Add expression for y: y = (+ a 1). Not a Variable → skipped.
    CoreExpr oneE;
    oneE.kind = Kind::ConstInt;
    oneE.sort = fx.intSort;
    oneE.payload = Payload(int64_t{1});
    ExprId oneId = fx.ir.addShared(std::move(oneE));
    ExprId aId = mkVarExpr(fx.ir, "a", fx.intSort);
    CoreExpr addE;
    addE.kind = Kind::Add;
    addE.sort = fx.intSort;
    addE.children = {aId, oneId};
    ExprId addId = fx.ir.addShared(std::move(addE));

    ModEqConstFact fact;
    fact.xExpr = fx.xExpr;
    fact.yExpr = addId;  // not Kind::Variable
    fact.c = 5;
    fact.atomExpr = fx.xyAtomExpr;
    fact.reason = makeLit(100);

    ModEqConstFactList facts{fact};
    DomainStore domains;
    domains.addLowerBound("a", 1, makeLit(101));

    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::NoChange);
}

TEST_CASE("ModEqConstReasoner: empty fact list is NoChange") {
    Fixture fx;
    ModEqConstReasoner r(*fx.kernel, fx.ir);
    ModEqConstFactList facts;
    DomainStore domains;
    auto result = r.run(facts, domains);
    CHECK(result.kind == NiaReasoningKind::NoChange);
}

}  // namespace xolver
