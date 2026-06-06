#include <doctest/doctest.h>
#include "theory/arith/nia/reasoners/DioReasoner.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/presolve/IntegerLinearAlgebra.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <optional>

using namespace xolver;

static SatLit mkReason(SatVar v) { return SatLit::positive(v); }
static PolyId pcst(PolynomialKernel& k, long c) { return k.mkConst(mpq_class(c)); }
static PolyId pscaled(PolynomialKernel& k, long c, PolyId p) { return k.mul(pcst(k, c), p); }

static const char* TWO32 = "4294967296";  // 2^32 — far above ModularResidueReasoner's 2^18 cap

// x - y - 3 = 0  with  x ≡ 0 (mod 2^32) and y ≡ 0 (mod 2^32)  forces
// (0 - 0 - 3) ≡ 0 (mod 2^32), i.e. -3 ≡ 0 (mod 2^32): false => UNSAT.
// ModularResidueReasoner cannot ENUMERATE mod 2^32; this is symbolic.
TEST_CASE("Dio-mod: x-y-3=0 with x,y ≡0 mod 2^32 -> Conflict (symbolic, large modulus)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy)), pcst(*kernel, 3));
    mpz_class m(TWO32);
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), m, mkReason(2)},
                      {vy, mpz_class(0), m, mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// With coefficients: 2x - y - 1 = 0, x,y ≡ 0 (mod 4) -> (0 - 0 - 1) = -1 ≢ 0 (mod 4) => Conflict.
TEST_CASE("Dio-mod: 2x-y-1=0 with x,y ≡0 mod 4 -> Conflict") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(pscaled(*kernel, 2, kernel->mkVar(vx)), kernel->mkVar(vy)),
                           pcst(*kernel, 1));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(4), mkReason(2)},
                      {vy, mpz_class(0), mpz_class(4), mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
}

// Soundness: a satisfiable modular system must NOT refute.
// x - y = 0 with x,y ≡ 0 (mod 4) -> 0 ≡ 0 (mod 4): consistent => NoChange.
TEST_CASE("Dio-mod: x-y=0 with x,y ≡0 mod 4 -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(4), mkReason(2)},
                      {vy, mpz_class(0), mpz_class(4), mkReason(3)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// Soundness: if a variable lacks a congruence the equality cannot be reduced
// (slack remains) -> NoChange.  x - y - 3 = 0 with only x ≡ 0 (mod 2^32).
TEST_CASE("Dio-mod: missing congruence -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId vx = kernel->getOrCreateVar("x"), vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->sub(kernel->sub(kernel->mkVar(vx), kernel->mkVar(vy)), pcst(*kernel, 3));
    auto res = r.run({{p, Relation::Eq, mkReason(1)}},
                     {{vx, mpz_class(0), mpz_class(TWO32), mkReason(2)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// --- Increment #9a: PROPAGATE a congruence through an equality chain ---

// a-b=0, b-c=0, c-3=0  with only  a ≡ 0 (mod 4) given.
// Propagation: a≡0 & a-b=0 => b≡0; b-c=0 => c≡0; then c-3=0 => -3 ≢ 0 (mod 4) => UNSAT.
// (The reasoner must DERIVE b,c's congruences, not just use the handed-in one.)
TEST_CASE("Dio-mod: propagate a≡0 through a=b=c chain, c=3 -> Conflict") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId va = kernel->getOrCreateVar("a"), vb = kernel->getOrCreateVar("b"),
          vc = kernel->getOrCreateVar("c");
    PolyId ab = kernel->sub(kernel->mkVar(va), kernel->mkVar(vb));            // a-b
    PolyId bc = kernel->sub(kernel->mkVar(vb), kernel->mkVar(vc));            // b-c
    PolyId c3 = kernel->sub(kernel->mkVar(vc), pcst(*kernel, 3));             // c-3
    auto res = r.run({{ab, Relation::Eq, mkReason(1)},
                      {bc, Relation::Eq, mkReason(2)},
                      {c3, Relation::Eq, mkReason(3)}},
                     {{va, mpz_class(0), mpz_class(4), mkReason(4)}});
    CHECK(res.kind == NiaReasoningKind::Conflict);
    REQUIRE(res.conflict.has_value());
}

// Soundness: same chain but c = 4 (≡ 0 mod 4) is consistent -> NoChange.
TEST_CASE("Dio-mod: propagate a≡0 through chain, c=4 -> NoChange (sound)") {
    auto kernel = createPolynomialKernel();
    DioReasoner r(*kernel);
    VarId va = kernel->getOrCreateVar("a"), vb = kernel->getOrCreateVar("b"),
          vc = kernel->getOrCreateVar("c");
    PolyId ab = kernel->sub(kernel->mkVar(va), kernel->mkVar(vb));
    PolyId bc = kernel->sub(kernel->mkVar(vb), kernel->mkVar(vc));
    PolyId c4 = kernel->sub(kernel->mkVar(vc), pcst(*kernel, 4));
    auto res = r.run({{ab, Relation::Eq, mkReason(1)},
                      {bc, Relation::Eq, mkReason(2)},
                      {c4, Relation::Eq, mkReason(3)}},
                     {{va, mpz_class(0), mpz_class(4), mkReason(4)}});
    CHECK(res.kind == NiaReasoningKind::NoChange);
}

// --- Increment #9b: lattice-step + bound tightening core (the in-de42 shape) ---
//
// The pure math: given an integer equality system A·x=b over columns, optional
// per-column bounds, and a linear form (Σ w·x + c), decide whether every
// (A x=b, lo≤x≤hi) forces the form to 0 — so asserting `form ≠ 0` is UNSAT.
// (z3's arith-dio-tighten; reuses smithNormalForm + a bound hull.)

using OptZ = std::optional<mpz_class>;

// in-de42 distilled: cols [r_z, r_n, t]; equality r_z - 2·r_n - M·t = 0;
// bounds 0≤r_z≤M-1, 0≤r_n≤M/2-1, t unbounded; form = r_z - 2·r_n.
// Lattice: form ∈ M·ℤ; hull [-(M-2), M-1] ∩ M·ℤ = {0} ⇒ form forced to 0.
TEST_CASE("Dio-lattice: r_z-2r_n=M·t, tight bounds force form=0 -> conflict") {
    mpz_class M(TWO32);
    IntMatrix A = {{mpz_class(1), mpz_class(-2), -M}};
    std::vector<mpz_class> b = {mpz_class(0)};
    std::vector<OptZ> lo = {mpz_class(0), mpz_class(0), std::nullopt};
    std::vector<OptZ> hi = {M - 1, M / 2 - 1, std::nullopt};
    std::vector<mpz_class> formW = {mpz_class(1), mpz_class(-2), mpz_class(0)};
    CHECK(DioReasoner::latticeForcesFormZero(A, b, lo, hi, formW, mpz_class(0)));
}

// Soundness: widen r_z's upper bound to 2M so the hull also contains M
// (another lattice point of the form) — form is NOT forced to 0.
TEST_CASE("Dio-lattice: loose bounds admit a 2nd lattice point -> no conflict (sound)") {
    mpz_class M(TWO32);
    IntMatrix A = {{mpz_class(1), mpz_class(-2), -M}};
    std::vector<mpz_class> b = {mpz_class(0)};
    std::vector<OptZ> lo = {mpz_class(0), mpz_class(0), std::nullopt};
    std::vector<OptZ> hi = {2 * M, M / 2 - 1, std::nullopt};
    std::vector<mpz_class> formW = {mpz_class(1), mpz_class(-2), mpz_class(0)};
    CHECK_FALSE(DioReasoner::latticeForcesFormZero(A, b, lo, hi, formW, mpz_class(0)));
}

// Soundness: an unbounded form variable means no hull can be computed -> no conflict.
TEST_CASE("Dio-lattice: unbounded form variable -> no conflict (sound)") {
    mpz_class M(TWO32);
    IntMatrix A = {{mpz_class(1), mpz_class(-2), -M}};
    std::vector<mpz_class> b = {mpz_class(0)};
    std::vector<OptZ> lo = {std::nullopt, mpz_class(0), std::nullopt};
    std::vector<OptZ> hi = {std::nullopt, M / 2 - 1, std::nullopt};
    std::vector<mpz_class> formW = {mpz_class(1), mpz_class(-2), mpz_class(0)};
    CHECK_FALSE(DioReasoner::latticeForcesFormZero(A, b, lo, hi, formW, mpz_class(0)));
}

// Soundness: form forced to a UNIQUE NONZERO value (x ≡ 1 mod 4, 0≤x≤3 ⇒ x=1).
// `form ≠ 0` is then satisfiable (form=1) -> must NOT conflict.
TEST_CASE("Dio-lattice: form forced to nonzero -> no conflict (sound)") {
    IntMatrix A = {{mpz_class(1), mpz_class(-4)}};   // x - 4t = 1
    std::vector<mpz_class> b = {mpz_class(1)};
    std::vector<OptZ> lo = {mpz_class(0), std::nullopt};
    std::vector<OptZ> hi = {mpz_class(3), std::nullopt};
    std::vector<mpz_class> formW = {mpz_class(1), mpz_class(0)};  // form = x
    CHECK_FALSE(DioReasoner::latticeForcesFormZero(A, b, lo, hi, formW, mpz_class(0)));
}

// --- Increment #9c: the shared string-keyed tightenConflict glue ---

using DZB = DioVarBound;
static DioLinForm form(std::vector<std::pair<std::string, long>> ts, long c, SatVar reasonVar) {
    DioLinForm f; f.cst = c; f.reason = SatLit::positive(reasonVar);
    for (auto& [v, a] : ts) f.coeffs.emplace_back(v, mpz_class(a));
    return f;
}

// in-de42 distilled at the glue level: eq  r_z - 2·r_n - M·t = 0,
// bounds 0≤r_z≤M-1, 0≤r_n≤M/2-1, diseq r_z - 2·r_n ≠ 0 -> conflict.
TEST_CASE("Dio-tighten: in-de42 distilled (eq + bounds + diseq) -> conflict") {
    mpz_class M(TWO32);
    std::vector<DioLinForm> eqs = {[&]{
        DioLinForm f; f.cst = 0; f.reason = SatLit::positive(1);
        f.coeffs = {{"r_z", mpz_class(1)}, {"r_n", mpz_class(-2)}, {"t", -M}};
        return f; }()};
    std::vector<DioLinForm> neqs = {form({{"r_z", 1}, {"r_n", -2}}, 0, 2)};
    std::map<std::string, DZB> bnds;
    bnds["r_z"] = DZB{true, true, mpz_class(0), M - 1, {SatLit::positive(3)}, {SatLit::positive(4)}};
    bnds["r_n"] = DZB{true, true, mpz_class(0), M / 2 - 1, {SatLit::positive(5)}, {SatLit::positive(6)}};
    auto c = DioReasoner::tightenConflict(eqs, neqs, bnds);
    REQUIRE(c.has_value());
    CHECK_FALSE(c->empty());
}

// Soundness: no disequality -> nothing forced -> nullopt.
TEST_CASE("Dio-tighten: no disequality -> nullopt (sound)") {
    mpz_class M(TWO32);
    std::vector<DioLinForm> eqs = {[&]{
        DioLinForm f; f.cst = 0; f.reason = SatLit::positive(1);
        f.coeffs = {{"r_z", mpz_class(1)}, {"r_n", mpz_class(-2)}, {"t", -M}};
        return f; }()};
    std::map<std::string, DZB> bnds;
    bnds["r_z"] = DZB{true, true, mpz_class(0), M - 1, {SatLit::positive(3)}, {SatLit::positive(4)}};
    bnds["r_n"] = DZB{true, true, mpz_class(0), M / 2 - 1, {SatLit::positive(5)}, {SatLit::positive(6)}};
    CHECK_FALSE(DioReasoner::tightenConflict(eqs, {}, bnds).has_value());
}

// Soundness: same eq+diseq but r_z unbounded -> no hull -> nullopt.
TEST_CASE("Dio-tighten: unbounded form var -> nullopt (sound)") {
    mpz_class M(TWO32);
    std::vector<DioLinForm> eqs = {[&]{
        DioLinForm f; f.cst = 0; f.reason = SatLit::positive(1);
        f.coeffs = {{"r_z", mpz_class(1)}, {"r_n", mpz_class(-2)}, {"t", -M}};
        return f; }()};
    std::vector<DioLinForm> neqs = {form({{"r_z", 1}, {"r_n", -2}}, 0, 2)};
    std::map<std::string, DZB> bnds;
    bnds["r_n"] = DZB{true, true, mpz_class(0), M / 2 - 1, {SatLit::positive(5)}, {SatLit::positive(6)}};
    CHECK_FALSE(DioReasoner::tightenConflict(eqs, neqs, bnds).has_value());
}

// Bound-infeasible: equalities + bounds admit NO solution (form lattice ∩ hull
// empty) -> sound to conflict (the system is UNSAT regardless of the diseq).
TEST_CASE("Dio-lattice: form lattice misses the hull entirely -> conflict") {
    // x - 4·t = 1  (so x ≡ 1 mod 4) with 0≤x≤3 has solution x=1; force a MISS:
    // x - 4·t = 0 (x ≡ 0 mod 4) with 2≤x≤3 -> no multiple of 4 in [2,3] -> empty.
    IntMatrix A = {{mpz_class(1), mpz_class(-4)}};
    std::vector<mpz_class> b = {mpz_class(0)};
    std::vector<OptZ> lo = {mpz_class(2), std::nullopt};
    std::vector<OptZ> hi = {mpz_class(3), std::nullopt};
    std::vector<mpz_class> formW = {mpz_class(1), mpz_class(0)};  // form = x
    CHECK(DioReasoner::latticeForcesFormZero(A, b, lo, hi, formW, mpz_class(0)));
}
