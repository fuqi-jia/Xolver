#include "nlcolver/Solver.h"
#include "nlcolver/Result.h"
#include "expr/ir.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "sat/Atomizer.h"
#include "theory/TheoryManager.h"
#include "theory/arith/lra/SimplexSolver.h"
#include "theory/arith/cad/CdcacSolver.h"
#include "theory/arith/poly/PolynomialKernel.h"

#include <somtparser/frontend/parser.h>

#include <iostream>
#include <unordered_map>

namespace nlcolver {

// ---------------------------------------------------------------------------
// Solver::Impl
// ---------------------------------------------------------------------------

class Solver::Impl {
public:
    std::string logic = "ALL";
    std::unordered_map<std::string, OptionValue> options;

    std::unique_ptr<SOMTParser::Parser> parser;
    std::unique_ptr<CoreIr> ir;
    std::unique_ptr<SatSolver> sat;
    TheoryManager theoryManager_;

    Impl() : sat(createSatSolver()) {
        theoryManager_.registerSolver(std::make_unique<SimplexSolver>());
        theoryManager_.registerSolver(std::make_unique<CdcacSolver>(createPolynomialKernel()));
    }

    void reset() {
        parser = std::make_unique<SOMTParser::Parser>();
        ir.reset();
        theoryManager_.reset();
    }

    bool parseFile(std::string_view filename) {
        parser = std::make_unique<SOMTParser::Parser>();
        if (!parser->parse(std::string(filename))) {
            return false;
        }
        FrontendAdapter adapter(*parser);
        ir = adapter.importProblem();
        return true;
    }

    Result checkSatInternal() {
        if (!ir) {
            return Result::Sat;
        }
        if (ir->assertions().empty()) {
            return Result::Sat;
        }

        // Reset SAT solver for fresh query.
        sat = createSatSolver();

        // Apply solver options (seed, etc.)
        auto itSeed = options.find("seed");
        if (itSeed != options.end() && itSeed->second.kind == OptionValue::Int) {
            sat->configure("seed", itSeed->second.i);
        }

        // Stage C/E: CDCL(T) loop.
        Atomizer atomizer(*sat);
        for (ExprId assertion : ir->assertions()) {
            SatLit lit = atomizer.atomize(assertion, *ir);
            sat->addClause({lit});
        }

        // Theory check loop (MVP: single iteration, no lemma learning)
        while (true) {
            SatSolver::SolveResult sr = sat->solve();
            if (sr == SatSolver::SolveResult::Unsat) {
                return Result::Unsat;
            }
            if (sr == SatSolver::SolveResult::Unknown) {
                return Result::Unknown;
            }

            // SAT model found → ask theories.
            auto tr = theoryManager_.check(*ir, atomizer.atoms(), *sat);

            if (tr.kind == TheoryCheckResult::Kind::Consistent) {
                return Result::Sat;
            }

            if (tr.kind == TheoryCheckResult::Kind::Conflict) {
                if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
                    sat->addClause(tr.conflictOpt->clause);
                    continue; // retry with conflict clause
                }
                return Result::Unknown;
            }

            if (tr.kind == TheoryCheckResult::Kind::Lemma) {
                if (tr.lemmaOpt && !tr.lemmaOpt->lits.empty()) {
                    sat->addClause(tr.lemmaOpt->lits);
                    continue; // retry with lemma
                }
                return Result::Unknown;
            }

            // Unknown
            return Result::Unknown;
        }
    }
};

// ---------------------------------------------------------------------------
// Solver public API
// ---------------------------------------------------------------------------

Solver::Solver() : pImpl(std::make_unique<Impl>()) {
    pImpl->reset();
}

Solver::~Solver() = default;

void Solver::reset() { pImpl->reset(); }

bool Solver::parseFile(std::string_view filename) {
    return pImpl->parseFile(filename);
}

void Solver::push() {
    if (pImpl->ir) pImpl->ir->pushScope();
}

void Solver::pop(uint32_t n) {
    if (pImpl->ir) {
        for (uint32_t i = 0; i < n; ++i) pImpl->ir->popScope();
    }
}

void Solver::setLogic(std::string_view logic) {
    pImpl->logic = std::string(logic);
}

void Solver::setOption(std::string_view key, OptionValue value) {
    pImpl->options[std::string(key)] = std::move(value);
}

OptionValue Solver::getOption(std::string_view key) const {
    auto it = pImpl->options.find(std::string(key));
    if (it != pImpl->options.end()) return it->second;
    return OptionValue(false);
}

Sort Solver::boolSort() { return Sort{}; /* TODO */ }
Sort Solver::intSort()  { return Sort{}; /* TODO */ }
Sort Solver::realSort() { return Sort{}; /* TODO */ }
Sort Solver::bvSort(uint32_t) { return Sort{}; /* TODO */ }
Sort Solver::fpSort(uint32_t, uint32_t) { return Sort{}; /* TODO */ }

Term Solver::mkConst(Sort, std::string_view) { return Term{}; /* TODO */ }
Term Solver::mkVar(Sort, std::string_view)   { return Term{}; /* TODO */ }
Term Solver::mkBool(bool)                    { return Term{}; /* TODO */ }
Term Solver::mkInt(int64_t)                  { return Term{}; /* TODO */ }
Term Solver::mkReal(const std::string&)      { return Term{}; /* TODO */ }
Term Solver::mkOp(uint32_t, std::vector<Term>) { return Term{}; /* TODO */ }

void Solver::assertFormula(Term) {
    // TODO: build term and assert
}

Result Solver::checkSat() {
    return pImpl->checkSatInternal();
}

Result Solver::checkSatAssuming(std::vector<Term>) {
    return Result::Unknown;
}

Model Solver::getModel() const { return Model{}; }
Term Solver::getValue(Term) const { return Term{}; }
std::vector<Term> Solver::getUnsatCore() const { return {}; }
Proof Solver::getProof() const { return Proof{}; }
Statistics Solver::getStatistics() const { return Statistics{}; }

void Solver::dumpSMT2(std::ostream& os) {
    if (pImpl->parser) {
        for (auto& a : pImpl->parser->getAssertions()) {
            os << SOMTParser::dumpSMTLIB2(a) << "\n";
        }
    }
}

} // namespace nlcolver
