#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "applications/satisfiability/smt/qfnia/NiaLinearDecider.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/boolean/Atomizer.h"
#include "search/coordination/TheoryManager.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

namespace {
// The linear decider can register branch atoms; even direct component tests
// need the same SAT/observation context as a production theory instance.
struct LinearDeciderContext {
    std::unique_ptr<SatSolver> sat = createSatSolver();
    Atomizer atomizer{*sat};
    TheoryAtomRegistry registry;
    TheoryManager theories;
    TheoryLemmaDatabase lemmas;
    CadicalBackend& backend = dynamic_cast<CadicalBackend&>(*sat);
    CadicalTheoryPropagator propagator{registry, theories, lemmas, backend};

    LinearDeciderContext() {
        registry.setContext(sat.get(), &atomizer);
        backend.connectPropagator(&propagator);
    }
    ~LinearDeciderContext() { backend.disconnectPropagator(); }
    SatLit reason() { return SatLit::positive(sat->newVar()); }
};
}

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_nia.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("NIA: polynomial definitions compose with rewriting and preserve query state") {
    const auto path = writeTempSmt2(
        "(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)(declare-const t Int)"
        "(assert (>= x 1))(assert (>= y 1))"
        "(assert (= t (+ (* x x x x) x)))"
        "(assert (= t (+ (* y y y y) x)))(assert (distinct x y))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    CHECK((solver.checkSat() == Result::Unsat));
    CHECK((solver.checkSat() == Result::Unsat));
}

TEST_CASE("NIA: even powers keep opposite sign models through substitution and push pop") {
    const auto path = writeTempSmt2(
        "(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)(declare-const t Int)"
        "(assert (= t (* x x)))(assert (= t (* y y)))"
        "(assert (= x (- 2)))(assert (distinct x y))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    for (int repeat = 0; repeat < 2; ++repeat) {
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
        solver.push();
        solver.assertFormula(solver.mkBool(false));
        CHECK((solver.checkSat() == Result::Unsat));
        solver.pop();
    }
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("NIA: trivial constant unsat (= 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: trivial constant sat (> 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (> 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: non-constant returns Unknown (= (* x x) 2)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 2))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // NIA-Core: UnivariateIntegerReasoner proves x^2=2 has no integer roots (UNSAT)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false literal negation (not (> 1 0)) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (> 1 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: distinct constant unsat (distinct 1 1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (distinct 1 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: eq negation constant unsat (not (= 1 1))") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (= 1 1)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: non-integer rational constant returns Unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= (/ 1 2) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: linear atom goes through polynomial path -> Sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // Linear constraint x>=0 is satisfiable (e.g. x=0)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ===========================================================================
// Category F: Strict inequality end-to-end
// ===========================================================================

TEST_CASE("NIA: strict Lt (< x 5) -> sat (x=4)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 5))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Gt (> x 0) -> sat (x=1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (> x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Lt + Gt direct conflict (< x 3) + (> x 3) -> unsat") {
    // Normalizes to: x <= 2 and x >= 4 → direct empty-domain conflict
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 3))\n"
        "(assert (> x 3))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: strict nonlinear (< (* x x) 0) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< (* x x) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ===========================================================================
// Category H: False literal effective relation regression
// ===========================================================================

TEST_CASE("NIA: false Leq effective relation (not (<= x 0)) + (<= x 0) -> unsat") {
    // not(x <= 0) means x > 0, which normalizes to x >= 1.
    // Together with x <= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (<= x 0)))\n"
        "(assert (<= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false Geq effective relation (not (>= x 0)) + (>= x 0) -> unsat") {
    // not(x >= 0) means x < 0, which normalizes to x <= -1.
    // Together with x >= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (>= x 0)))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA linear-decide: preserves auxiliary and double-underscore variable values") {
    auto kernel = createPolynomialKernel();
    LinearDeciderContext context;
    auto& registry = context.registry;
    IntegerModelValidator validator(*kernel);
    NiaLinearDecider decider;
    const auto user = kernel->mkVar(kernel->getOrCreateVar("__user"));
    const auto witness = kernel->mkVar(kernel->getOrCreateVar("__nlc_ext_idx_0"));
    const std::vector<NormalizedNiaConstraint> constraints{
        {kernel->sub(user, kernel->mkConst(7)), Relation::Eq, context.reason()},
        {kernel->sub(witness, user), Relation::Eq, context.reason()}
    };
    auto model = decider.decide(&registry, *kernel, constraints, validator);
    REQUIRE(model.has_value());
    CHECK((validator.validate(*model, constraints) == IntegerModelValidator::Result::Valid));
    CHECK(model->at("__user") == 7);
    CHECK(model->at("__nlc_ext_idx_0") == 7);
}

TEST_CASE("NIA linear-decide: searches beyond integral points violating disequalities") {
    auto kernel = createPolynomialKernel();
    LinearDeciderContext context;
    auto& registry = context.registry;
    IntegerModelValidator validator(*kernel);
    NiaLinearDecider decider;
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const std::vector<NormalizedNiaConstraint> constraints{
        {x, Relation::Neq, context.reason()},
        {x, Relation::Geq, context.reason()},
        {kernel->sub(x, kernel->mkConst(1)), Relation::Neq, context.reason()},
        {kernel->sub(x, kernel->mkConst(2)), Relation::Leq, context.reason()}
    };
    auto model = decider.decide(&registry, *kernel, constraints, validator);
    REQUIRE(model.has_value());
    CHECK((validator.validate(*model, constraints) == IntegerModelValidator::Result::Valid));
    CHECK(model->at("x") == 2);
}

TEST_CASE("NIA: combination linear model covers wide modulus values") {
    // Exercise the normal pipeline and check its model against the original
    // array/mod formula. The linear decider is tested directly below.
    std::string path = writeTempSmt2(
        "(set-logic QF_ANIA)\n"
        "(declare-const A (Array Int Int))\n"
        "(declare-const r Int)\n"
        "(assert (= r (mod (+ (select A 0) (select A 1) (select A 2)) 4294967296)))\n"
        "(assert (> r 2147483647))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_ANIA");
    REQUIRE(solver.parseFile(path));
    Result r = solver.checkSat();
    REQUIRE(static_cast<int>(r) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("NIA: infeasible linear branch does not refute the satisfiable formula") {
    // An infeasible Boolean branch must not become a global UNSAT verdict.
    // The other branch has a wide-modulus witness. Direct component coverage
    // below separately checks the linear decider's conflict reasons.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const b Bool)\n"
        "(assert (ite b\n"
        "  (< 2147483647 (mod (+ x y) 4294967296))\n"
        "  (and (= x 5) (= x 6))))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_NIA");
    REQUIRE(solver.parseFile(path));
    Result r = solver.checkSat();
    REQUIRE(static_cast<int>(r) == static_cast<int>(Result::Sat));
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("NIA linear-decide: wide modulus linkage has an exact integer witness") {
    auto kernel = createPolynomialKernel();
    LinearDeciderContext context;
    auto& registry = context.registry;
    IntegerModelValidator validator(*kernel);
    NiaLinearDecider decider;
    const auto x = kernel->mkVar(kernel->getOrCreateVar("array_read"));
    const auto q = kernel->mkVar(kernel->getOrCreateVar("__quotient"));
    const auto r = kernel->mkVar(kernel->getOrCreateVar("__remainder"));
    const mpz_class modulus = mpz_class(1) << 32;
    const mpz_class lower = mpz_class(1) << 31;
    const auto linkage = kernel->sub(kernel->sub(x, kernel->mul(kernel->mkConst(mpq_class(modulus)), q)), r);
    const std::vector<NormalizedNiaConstraint> cs{
        {linkage, Relation::Eq, context.reason()},
        {kernel->sub(r, kernel->mkConst(mpq_class(lower))), Relation::Geq, context.reason()},
        {kernel->sub(r, kernel->mkConst(mpq_class(modulus - 1))), Relation::Leq, context.reason()}};
    const auto model = decider.decide(&registry, *kernel, cs, validator);
    REQUIRE(model.has_value());
    CHECK(model->at("array_read") == modulus * model->at("__quotient") + model->at("__remainder"));
    CHECK(model->at("__remainder") >= lower);
    CHECK(model->at("__remainder") < modulus);
}

TEST_CASE("NIA linear-decide: root conflict carries exactly the asserted branch reasons") {
    auto kernel = createPolynomialKernel();
    LinearDeciderContext context;
    auto& registry = context.registry;
    IntegerModelValidator validator(*kernel);
    NiaLinearDecider decider;
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto first = context.reason(), second = context.reason();
    const std::vector<NormalizedNiaConstraint> cs{
        {kernel->sub(x, kernel->mkConst(5)), Relation::Eq, first},
        {kernel->sub(x, kernel->mkConst(6)), Relation::Eq, second}};
    std::optional<TheoryConflict> conflict;
    CHECK_FALSE(decider.decide(&registry, *kernel, cs, validator, &conflict).has_value());
    REQUIRE(conflict.has_value());
    REQUIRE(conflict->clause.size() == 2);
    for (const auto& literal : conflict->clause) {
        CHECK((literal == first || literal == second));
    }
}
