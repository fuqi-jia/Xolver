#include <doctest/doctest.h>
#include "contracts/SatSolver.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <array>
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

TEST_CASE("Encoder: majority gates preserve every input polarity and constant") {
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder enc(*sat);
    const std::array variables{sat->newVar(), sat->newVar(), sat->newVar()};
    const std::array choices{
        SatLit::positive(variables[0]), SatLit::negative(variables[0]),
        SatLit::positive(variables[1]), SatLit::negative(variables[1]),
        SatLit::positive(variables[2]), SatLit::negative(variables[2]),
        enc.constTrue(), enc.constFalse()};
    struct Predicate { unsigned a, b, c; SatLit output; };
    std::vector<Predicate> predicates;
    for (unsigned a = 0; a < choices.size(); ++a)
        for (unsigned b = 0; b < choices.size(); ++b)
            for (unsigned c = 0; c < choices.size(); ++c)
                predicates.push_back({a, b, c, enc.majorityGate(choices[a], choices[b], choices[c])});
    auto inputValue = [](unsigned choice, unsigned mask) {
        if (choice >= 6) return choice == 6;
        const bool value = mask & (1u << (choice / 2));
        return choice % 2 ? !value : value;
    };
    for (unsigned mask = 0; mask < 8; ++mask) {
        std::vector<SatLit> assumptions;
        for (unsigned i = 0; i < variables.size(); ++i)
            assumptions.emplace_back(variables[i], bool(mask & (1u << i)));
        REQUIRE(sat->solve(assumptions) == SatSolver::SolveResult::Sat);
        std::vector<bool> observed;
        for (const auto& p : predicates) observed.push_back(bitblast::litValue(*sat, p.output));
        for (size_t i = 0; i < predicates.size(); ++i) {
            const auto& p = predicates[i];
            const bool expected = unsigned(inputValue(p.a, mask)) + unsigned(inputValue(p.b, mask)) +
                                  unsigned(inputValue(p.c, mask)) >= 2;
            CHECK(observed[i] == expected);
            assumptions.push_back(expected ? p.output.negated() : p.output);
            CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
            assumptions.pop_back();
        }
    }
}

TEST_CASE("Encoder: ternary sharing preserves all variable bits and the fresh allocation budget") {
    for (SatVar high : {(SatVar(1) << 30) + 3, (SatVar(1) << 31) + 3,
                        std::numeric_limits<SatVar>::max()}) {
        for (unsigned polarity = 0; polarity < 8; ++polarity) {
            SparseSat sat;
            bitblast::BitBlastEncoder enc(sat);
            const auto a = sat.newVar(), b = sat.newVar(), c = sat.newVar();
            sat.bind(high);
            const SatLit al(a, polarity & 1), bl(b, polarity & 2);
            const SatLit cl(c, polarity & 4), hl(high, polarity & 4);
            const std::array low{enc.iteGate(al, bl, cl), enc.majorityGate(al, bl, cl)};
            const std::array wide{enc.iteGate(al, bl, hl), enc.majorityGate(al, bl, hl)};
            const auto count = enc.varCount();
            const auto clauses = sat.clauses;
            CHECK(low[0] != low[1]);
            CHECK(wide[0] != wide[1]);
            CHECK(enc.iteGate(al.negated(), cl, bl) == low[0]);
            CHECK(enc.majorityGate(cl, al, bl) == low[1]);
            CHECK(enc.iteGate(al, bl, hl) == wide[0]);
            CHECK(enc.majorityGate(hl, bl, al) == wide[1]);
            CHECK(enc.varCount() == count);
            CHECK(sat.clauses == clauses);
            CHECK(enc.ternaryCacheHits() >= 4);
            for (unsigned mask = 0; mask < 16; ++mask) {
                const bool av = bool(mask & 1) == al.sign, bv = bool(mask & 2) == bl.sign;
                const bool cv = bool(mask & 4) == cl.sign, hv = bool(mask & 8) == hl.sign;
                const std::array expected{av ? bv : cv, unsigned(av) + unsigned(bv) + unsigned(cv) >= 2,
                                          av ? bv : hv, unsigned(av) + unsigned(bv) + unsigned(hv) >= 2};
                const std::array outputs{low[0], low[1], wide[0], wide[1]};
                std::vector<SatLit> good{{a, bool(mask & 1)}, {b, bool(mask & 2)},
                                         {c, bool(mask & 4)}, {high, bool(mask & 8)}};
                for (size_t i = 0; i < outputs.size(); ++i)
                    good.push_back(expected[i] ? outputs[i] : outputs[i].negated());
                REQUIRE(sat.solve(good) == SatSolver::SolveResult::Sat);
                for (size_t i = 0; i < outputs.size(); ++i) {
                    good[4 + i] = good[4 + i].negated();
                    CHECK(sat.solve(good) == SatSolver::SolveResult::Unsat);
                    good[4 + i] = good[4 + i].negated();
                }
            }
            enc.setVarBudget(count);
            CHECK(enc.majorityGate(bl, cl, al) == low[1]);
            CHECK_FALSE(enc.overflowed());
            enc.iteGate(SatLit::positive(a), SatLit::positive(c), SatLit::positive(high));
            CHECK(enc.overflowed());
            CHECK(enc.varCount() == count);
        }
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
