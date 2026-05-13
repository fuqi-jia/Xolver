#include "nlcolver/Solver.h"
#include "nlcolver/Result.h"
#include "expr/ir.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "sat/Atomizer.h"
#include "theory/TheoryManager.h"
#include "theory/TheoryLemmaDatabase.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/arith/lra/LraSolver.h"
#include "theory/arith/lia/LiaSolver.h"
#include "theory/arith/nra/NraSolver.h"
#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/idl/IdlSolver.h"
#include "theory/arith/rdl/RdlSolver.h"
#include "theory/arith/poly/PolynomialKernel.h"

#ifdef NLCOLVER_HAS_CADICAL
#include "sat/CadicalBackend.h"
#include "sat/CadicalTheoryPropagator.h"
#endif

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

    Impl() : sat(createSatSolver()) {}

    void reset() {
        parser = std::make_unique<SOMTParser::Parser>();
        ir.reset();
        sat.reset();
    }

    bool parseFile(std::string_view filename) {
        parser = std::make_unique<SOMTParser::Parser>();
        if (!parser->parse(std::string(filename))) {
            return false;
        }
        // Auto-detect logic from the parsed file.
        auto opts = parser->getOptions();
        if (opts && opts->logic != "UNKNOWN_LOGIC" && opts->logic != "ALL") {
            logic = opts->logic;
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

#ifndef NLCOLVER_HAS_CADICAL
        return Result::Unknown;
#else
        auto* cadicalBackend = dynamic_cast<CadicalBackend*>(sat.get());
        if (!cadicalBackend) {
            return Result::Unknown;
        }

        // Fresh per-check-sat instances
        TheoryAtomRegistry registry;
        TheoryManager theoryManager;
        TheoryLemmaDatabase lemmaDb;
        PolynomialKernel* polyKernelRaw = nullptr;

        // Register solvers based on logic.
        if (logic == "QF_LIA" || logic == "LIA") {
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            theoryManager.registerSolver(std::move(lia));
        } else if (logic == "QF_LRA" || logic == "LRA") {
            theoryManager.registerSolver(std::make_unique<LraSolver>());
        } else if (logic == "QF_NRA" || logic == "NRA") {
            auto polyKernel = createPolynomialKernel();
            polyKernelRaw = polyKernel.get();
            theoryManager.registerSolver(
                std::make_unique<NraSolver>(std::move(polyKernel)));
            theoryManager.registerSolver(std::make_unique<LraSolver>()); // co-register for linearizer cuts
        } else if (logic == "QF_NIA" || logic == "NIA") {
            auto polyKernel = createPolynomialKernel();
            polyKernelRaw = polyKernel.get();
            auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
            nia->setRegistry(&registry);
            theoryManager.registerSolver(std::move(nia));
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            theoryManager.registerSolver(std::move(lia));
        } else if (logic == "QF_IDL" || logic == "IDL") {
            auto idl = std::make_unique<IdlSolver>();
            idl->setRegistry(&registry);
            theoryManager.registerSolver(std::move(idl));
        } else if (logic == "QF_RDL" || logic == "RDL") {
            auto rdl = std::make_unique<RdlSolver>();
            rdl->setRegistry(&registry);
            theoryManager.registerSolver(std::move(rdl));
        } else {
            // Default: LRA covers most linear arithmetic; pure boolean works too.
            theoryManager.registerSolver(std::make_unique<LraSolver>());
        }

        // Connect propagator FIRST (required before addObservedVar)
        CadicalTheoryPropagator propagator(registry, theoryManager, lemmaDb, *cadicalBackend);
        cadicalBackend->connectPropagator(&propagator);

        // Atomizer registers parsed atoms into registry (which calls addObservedVar)
        Atomizer atomizer(*sat);
        registry.setContext(sat.get(), &atomizer);
        atomizer.setRegistry(&registry);

        if (logic == "QF_LIA" || logic == "LIA") {
            atomizer.setDefaultTheory(TheoryId::LIA);
        } else if (logic == "QF_NRA" || logic == "NRA") {
            atomizer.setDefaultTheory(TheoryId::NRA);
            // Atomizer and NraSolver must share the same PolynomialKernel instance.
            // NraSolver owns the kernel; Atomizer borrows a raw pointer.
            if (polyKernelRaw) {
                atomizer.setPolynomialKernel(polyKernelRaw);
            }
        } else if (logic == "QF_NIA" || logic == "NIA") {
            atomizer.setDefaultTheory(TheoryId::NIA);
            // Atomizer and NiaSolver must share the same PolynomialKernel instance.
            // NiaSolver owns the kernel; Atomizer borrows a raw pointer.
            if (polyKernelRaw) {
                atomizer.setPolynomialKernel(polyKernelRaw);
            }
        } else if (logic == "QF_IDL" || logic == "IDL") {
            atomizer.setDefaultTheory(TheoryId::IDL);
        } else if (logic == "QF_RDL" || logic == "RDL") {
            atomizer.setDefaultTheory(TheoryId::RDL);
        } else {
            atomizer.setDefaultTheory(TheoryId::LRA);
        }

        for (ExprId assertion : ir->assertions()) {
            SatLit lit = atomizer.atomize(assertion, *ir);
            sat->addClause({lit});
        }

        if (registry.hasUnsupportedTheoryAtom()) {
            cadicalBackend->disconnectPropagator();
            return Result::Unknown;
        }

        auto result = sat->solve();
        cadicalBackend->disconnectPropagator();

        if (result == SatSolver::SolveResult::Sat) return Result::Sat;
        if (result == SatSolver::SolveResult::Unsat) return Result::Unsat;
        return Result::Unknown;
#endif
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

Model Solver::getModel() const {
    // TODO: When model construction is implemented, filter out internal
    // variables such as "__ZERO__" used by difference-logic solvers.
    return Model{};
}
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
