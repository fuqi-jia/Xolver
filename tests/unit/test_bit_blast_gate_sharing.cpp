#include <doctest/doctest.h>
#include "contracts/SatSolver.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <limits>
#include <unordered_map>
using namespace xolver;

namespace {
// Map sparse public IDs injectively to a tiny real SAT instance, so boundary
// coverage does not require allocating billions of backend variables.
class SparseSat : public SatSolver {
    std::unique_ptr<SatSolver> inner = createSatSolver();
    std::unordered_map<SatVar,SatVar> ids;
    SatVar next = 1;
public:
    unsigned clauses = 0;
private:
    std::vector<SatLit> translate(const std::vector<SatLit>& xs) const {
        std::vector<SatLit> out;
        for (auto x:xs) out.emplace_back(ids.at(x.var),x.sign);
        return out;
    }
public:
    SatVar bind(SatVar external) { ids.emplace(external,inner->newVar()); return external; }
    SatVar newVar() override { while(ids.count(next)) ++next; return bind(next++); }
    void addClause(const std::vector<SatLit>& xs) override { ++clauses; inner->addClause(translate(xs)); }
    SolveResult solve() override { return inner->solve(); }
    SolveResult solve(const std::vector<SatLit>& xs) override { return inner->solve(translate(xs)); }
    bool value(SatVar v) const override { return inner->value(ids.at(v)); }
    void setDeadline(std::chrono::steady_clock::time_point d) override { inner->setDeadline(d); }
};
bool eval(unsigned type,bool a,bool b) { return type==0?(a&&b):type==1?(a||b):(a!=b); }
SatLit gate(bitblast::BitBlastEncoder& enc,unsigned type,SatLit a,SatLit b) {
    return type==0?enc.andGate(a,b):type==1?enc.orGate(a,b):enc.xorGate(a,b);
}
}

TEST_CASE("Encoder: gate sharing preserves truth tables across all variable ID bits") {
    for (SatVar high : { (SatVar(1) << 30) + 3, (SatVar(1) << 31) + 3,
                         std::numeric_limits<SatVar>::max() }) {
        for (unsigned type = 0; type < 3; ++type) {
            for (unsigned polarity = 0; polarity < 4; ++polarity) {
                CAPTURE(high); CAPTURE(type); CAPTURE(polarity);
                SparseSat sat;
                bitblast::BitBlastEncoder enc(sat);
                auto a = sat.newVar(), b = sat.newVar();
                sat.bind(high);
                SatLit al(a, polarity & 1), bl(b, polarity & 2), hl(high, polarity & 2);
                const auto low = gate(enc, type, al, bl);
                const auto wide = gate(enc, type, al, hl);
                for (unsigned mask = 0; mask < 8; ++mask) {
                    CAPTURE(mask);
                    bool av = mask & 1, bv = mask & 2, hv = mask & 4;
                    bool l = eval(type, av == al.sign, bv == bl.sign);
                    bool h = eval(type, av == al.sign, hv == hl.sign);
                    std::vector<SatLit> inputs{{a, av}, {b, bv}, {high, hv}};
                    auto good = inputs;
                    good.emplace_back(low.var, low.sign == l);
                    good.emplace_back(wide.var, wide.sign == h);
                    REQUIRE(sat.solve(good) == SatSolver::SolveResult::Sat);
                    // Check the converse as well: CNF must force both outputs.
                    auto bad = inputs;
                    bad.emplace_back(low.var, low.sign != l);
                    CHECK(sat.solve(bad) == SatSolver::SolveResult::Unsat);
                    bad.back() = SatLit(wide.var, wide.sign != h);
                    CHECK(sat.solve(bad) == SatSolver::SolveResult::Unsat);
                }
            }
        }
    }
}

TEST_CASE("Encoder: commuted gates share without conflating types or polarities") {
    SparseSat sat;
    bitblast::BitBlastEncoder enc(sat);
    const auto a = sat.newVar(), b = sat.newVar();
    for (unsigned type = 0; type < 3; ++type) {
        for (unsigned polarity = 0; polarity < 4; ++polarity) {
            SatLit al(a, polarity & 1), bl(b, polarity & 2);
            const auto output = gate(enc, type, al, bl);
            const auto count = enc.varCount();
            const auto clauses = sat.clauses;
            CHECK(gate(enc, type, bl, al) == output);
            CHECK(enc.varCount() == count);
            CHECK(sat.clauses == clauses);
            for (unsigned mask = 0; mask < 4; ++mask) {
                bool av = mask & 1, bv = mask & 2;
                bool expected = eval(type, av == al.sign, bv == bl.sign);
                std::vector<SatLit> good{{a,av}, {b,bv}, {output.var, output.sign == expected}};
                REQUIRE(sat.solve(good) == SatSolver::SolveResult::Sat);
                good.back() = good.back().negated();
                CHECK(sat.solve(good) == SatSolver::SolveResult::Unsat);
            }
        }
    }
    CHECK(enc.varCount() == 12);
}

TEST_CASE("Encoder: cached gates respect the fresh-variable resource budget") {
    for (unsigned type = 0; type < 3; ++type) {
        SparseSat sat;
        bitblast::BitBlastEncoder enc(sat);
        SatLit a = SatLit::positive(sat.newVar()), b = SatLit::positive(sat.newVar());
        enc.setVarBudget(1);
        const auto output = gate(enc, type, a, b);
        CHECK_FALSE(enc.overflowed());
        const auto clauses = sat.clauses;
        CHECK(gate(enc, type, b, a) == output);
        CHECK_FALSE(enc.overflowed());
        CHECK(enc.varCount() == 1);
        // A cache miss has no room for an output. It must mark overflow
        // without emitting clauses or caching a constant-false placeholder.
        gate(enc, (type + 1) % 3, a, b);
        CHECK(enc.overflowed());
        CHECK(enc.varCount() == 1);
        CHECK(sat.clauses == clauses);
    }
}
