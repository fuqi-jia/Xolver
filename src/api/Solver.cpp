#include "nlcolver/Solver.h"
#include "nlcolver/Result.h"
#include "expr/ir.h"
#include "expr/CoreIteLowerer.h"
#include "expr/Smt2Dumper.h"
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
#include "theory/arith/lira/LiraSolver.h"
#include "theory/arith/nira/NiraSolver.h"
#include "theory/arith/idl/IdlSolver.h"
#include "theory/arith/rdl/RdlSolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/euf/EufSolver.h"
#include "theory/combination/Purifier.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/LogicFeatureDetector.h"

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
    SortId boolSortId_ = NullSort;
    SortId intSortId_ = NullSort;
    SortId realSortId_ = NullSort;
    std::unique_ptr<SharedTermRegistry> sharedTermRegistry_;
    std::optional<TheorySolver::TheoryModel> lastModel_;
    std::vector<Term> lastAssumptions_;

    Impl() : sat(createSatSolver()) {}

    void reset() {
        parser = std::make_unique<SOMTParser::Parser>();
        ir.reset();
        sat.reset();
        sharedTermRegistry_.reset();
        boolSortId_ = NullSort;
        intSortId_ = NullSort;
        realSortId_ = NullSort;
        lastModel_.reset();
    }

    bool parseFile(std::string_view filename) {
        parser = std::make_unique<SOMTParser::Parser>();
        parser->setOption("expand_functions", true);
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
        boolSortId_ = adapter.getBoolSortId();
        intSortId_ = ir->intSortId();
        realSortId_ = ir->realSortId();
        return true;
    }

    CoreIr& ensureIr() {
        if (!ir) ir = std::make_unique<CoreIr>();
        return *ir;
    }

    SortId getOrCreateBoolSort() {
        if (boolSortId_ != NullSort) return boolSortId_;
        auto& cir = ensureIr();
        boolSortId_ = cir.allocateSortId();
        cir.registerSort(boolSortId_, SortKind::Bool);
        cir.setBoolSortId(boolSortId_);
        return boolSortId_;
    }

    SortId getOrCreateIntSort() {
        if (intSortId_ != NullSort) return intSortId_;
        auto& cir = ensureIr();
        intSortId_ = cir.allocateSortId();
        cir.registerSort(intSortId_, SortKind::Int);
        cir.setIntSortId(intSortId_);
        return intSortId_;
    }

    SortId getOrCreateRealSort() {
        if (realSortId_ != NullSort) return realSortId_;
        auto& cir = ensureIr();
        realSortId_ = cir.allocateSortId();
        cir.registerSort(realSortId_, SortKind::Real);
        cir.setRealSortId(realSortId_);
        return realSortId_;
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

        // Lower ITEs before any theory processing or atomization.
        // CoreIteLowerer is a pure IR-to-IR pass: no SatLit, no theory atom
        // registration, no SAT clause insertion.
        {
            CoreIteLowerer lowerer(*ir);
            auto originalScoped = ir->getScopedAssertions();
            std::vector<std::pair<ScopeLevel, ExprId>> loweredScoped;
            for (const auto& [level, a] : originalScoped) {
                loweredScoped.push_back({level, lowerer.lowerAssertion(a)});
            }
            for (ExprId def : lowerer.generatedAssertions()) {
                // Generated definitions belong to the current scope
                loweredScoped.push_back({ir->currentScopeLevel(), def});
            }
            ir->clearAssertions();
            for (const auto& [level, a] : loweredScoped) {
                ir->addAssertion(a, level);
            }
        }

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

        // Detect features from CoreIr for safe routing
        LogicFeatureDetector detector(*ir);
        LogicFeatures features = detector.detect();

        // -------------------------------------------------------------------
        // Mismatch guard: declared logic must cover detected features
        // -------------------------------------------------------------------
        bool logicMismatch = false;
        if (logic == "QF_LIA" || logic == "LIA") {
            if (features.hasRealVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_LRA" || logic == "LRA") {
            if (features.hasIntVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_NRA" || logic == "NRA") {
            if (features.hasIntVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_NIA" || logic == "NIA") {
            if (features.hasRealVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_IDL" || logic == "IDL") {
            if (features.hasRealVar || features.hasNonlinear || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_RDL" || logic == "RDL") {
            if (features.hasIntVar || features.hasNonlinear || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_UF" || logic == "UF") {
            if (features.hasIntVar || features.hasRealVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
            if (features.hasIntVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_LIRA" || logic == "LIRA") {
            if (features.hasNonlinear || features.hasUF) logicMismatch = true;
        } else if (logic == "QF_NIRA" || logic == "NIRA") {
            if (features.hasUF) logicMismatch = true;
        }

        if (logicMismatch) {
            std::cerr << "[Solver] declared logic '" << logic
                      << "' mismatches detected features ("
                      << "Bool=" << features.hasBool
                      << " Int=" << features.hasInt
                      << " Real=" << features.hasReal
                      << " UF=" << features.hasUF
                      << " NL=" << features.hasNonlinear
                      << " Mixed=" << features.hasMixedIntReal
                      << "). Returning Unknown.\n";
            return Result::Unknown;
        }

        if (features.hasUnsupported) {
            return Result::Unknown;
        }

        // -------------------------------------------------------------------
        // Register solvers based on logic or detected features
        // -------------------------------------------------------------------
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
        } else if (logic == "QF_LIRA" || logic == "LIRA") {
            auto lira = std::make_unique<LiraSolver>();
            lira->setRegistry(&registry);
            lira->setCoreIr(ir.get());
            theoryManager.registerSolver(std::move(lira));
        } else if (logic == "QF_NIRA" || logic == "NIRA") {
            auto polyKernel = createPolynomialKernel();
            polyKernelRaw = polyKernel.get();
            auto nira = std::make_unique<NiraSolver>(std::move(polyKernel));
            nira->setRegistry(&registry);
            nira->setCoreIr(ir.get());
            theoryManager.registerSolver(std::move(nira));
        } else if (logic == "QF_IDL" || logic == "IDL") {
            auto idl = std::make_unique<IdlSolver>();
            idl->setRegistry(&registry);
            theoryManager.registerSolver(std::move(idl));
        } else if (logic == "QF_RDL" || logic == "RDL") {
            auto rdl = std::make_unique<RdlSolver>();
            rdl->setRegistry(&registry);
            theoryManager.registerSolver(std::move(rdl));
        } else if (logic == "QF_UF") {
            auto euf = std::make_unique<EufSolver>();
            euf->setCoreIr(ir.get());
            theoryManager.registerSolver(std::move(euf));
        } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
            sharedTermRegistry_ = std::make_unique<SharedTermRegistry>();
            {
                Purifier purifier(*ir, *sharedTermRegistry_, boolSortId_);
                purifier.run();
            }
            auto euf = std::make_unique<EufSolver>();
            euf->setCoreIr(ir.get());
            euf->setSharedTermRegistry(sharedTermRegistry_.get());
            theoryManager.registerSolver(std::move(euf));
            auto lra = std::make_unique<LraSolver>();
            lra->setCoreIr(ir.get());
            lra->setSharedTermRegistry(sharedTermRegistry_.get());
            theoryManager.registerSolver(std::move(lra));
            theoryManager.setSharedTermRegistry(sharedTermRegistry_.get());
            theoryManager.setRegistry(&registry);
            theoryManager.setCombinationMode(true);
        } else if (logic == "QF_UFLIA" || logic == "UFLIA") {
            if (features.hasRealVar || features.hasNonlinear || features.hasMixedIntReal) {
                logicMismatch = true;
            } else {
                sharedTermRegistry_ = std::make_unique<SharedTermRegistry>();
                {
                    Purifier purifier(*ir, *sharedTermRegistry_, boolSortId_);
                    purifier.setArithTheory(TheoryId::LIA);
                    purifier.run();
                }
                auto euf = std::make_unique<EufSolver>();
                euf->setCoreIr(ir.get());
                euf->setSharedTermRegistry(sharedTermRegistry_.get());
                theoryManager.registerSolver(std::move(euf));
                auto lia = std::make_unique<LiaSolver>();
                lia->setCoreIr(ir.get());
                lia->setSharedTermRegistry(sharedTermRegistry_.get());
                lia->setRegistry(&registry);
                theoryManager.registerSolver(std::move(lia));
                theoryManager.setSharedTermRegistry(sharedTermRegistry_.get());
                theoryManager.setRegistry(&registry);
                theoryManager.setCombinationMode(true);
                theoryManager.setNonConvexMode(true);
            }
        } else if (logic == "QF_UFNIA" || logic == "QF_UFNRA" ||
                   logic == "UFNIA" || logic == "UFNRA" ||
                   logic == "UF") {
            // Mixed theories not supported in V1
            return Result::Unknown;
        } else {
            // No declared logic or unrecognized logic: route by detected features.
            // Use hasIntVar / hasRealVar (not hasInt / hasReal) to avoid
            // mis-routing caused by integer/real constant literals.
            if (features.hasUF) {
                return Result::Unknown; // combination not yet supported for auto-detect
            }
            if (features.hasMixedIntReal) {
                if (features.hasNonlinear) {
                    auto polyKernel = createPolynomialKernel();
                    polyKernelRaw = polyKernel.get();
                    auto nira = std::make_unique<NiraSolver>(std::move(polyKernel));
                    nira->setRegistry(&registry);
                    theoryManager.registerSolver(std::move(nira));
                } else {
                    auto lira = std::make_unique<LiraSolver>();
                    lira->setRegistry(&registry);
                    lira->setCoreIr(ir.get());
                    theoryManager.registerSolver(std::move(lira));
                }
            } else if (features.hasIntVar && features.hasNonlinear) {
                auto polyKernel = createPolynomialKernel();
                polyKernelRaw = polyKernel.get();
                auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
                nia->setRegistry(&registry);
                theoryManager.registerSolver(std::move(nia));
                auto lia = std::make_unique<LiaSolver>();
                lia->setRegistry(&registry);
                theoryManager.registerSolver(std::move(lia));
            } else if (features.hasIntVar) {
                auto lia = std::make_unique<LiaSolver>();
                lia->setRegistry(&registry);
                theoryManager.registerSolver(std::move(lia));
            } else if (features.hasRealVar && features.hasNonlinear) {
                auto polyKernel = createPolynomialKernel();
                polyKernelRaw = polyKernel.get();
                theoryManager.registerSolver(
                    std::make_unique<NraSolver>(std::move(polyKernel)));
                theoryManager.registerSolver(std::make_unique<LraSolver>());
            } else if (features.hasRealVar) {
                theoryManager.registerSolver(std::make_unique<LraSolver>());
            } else {
                // Pure boolean or empty: no theory solver needed
            }
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
        } else if (logic == "QF_LRA" || logic == "LRA") {
            atomizer.setDefaultTheory(TheoryId::LRA);
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
        } else if (logic == "QF_LIRA" || logic == "LIRA") {
            atomizer.setDefaultTheory(TheoryId::LIRA);
        } else if (logic == "QF_NIRA" || logic == "NIRA") {
            atomizer.setDefaultTheory(TheoryId::NIRA);
            if (polyKernelRaw) {
                atomizer.setPolynomialKernel(polyKernelRaw);
            }
        } else if (logic == "QF_IDL" || logic == "IDL") {
            atomizer.setDefaultTheory(TheoryId::IDL);
        } else if (logic == "QF_RDL" || logic == "RDL") {
            atomizer.setDefaultTheory(TheoryId::RDL);
        } else if (logic == "QF_UF") {
            atomizer.setDefaultTheory(TheoryId::EUF);
            atomizer.setBoolSortId(boolSortId_);
        } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setBoolSortId(boolSortId_);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
        } else if (logic == "QF_UFLIA" || logic == "UFLIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setBoolSortId(boolSortId_);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::LIA);
        } else {
            // No declared logic: route by detected features.
            // Use hasIntVar / hasRealVar (not hasInt / hasReal) to avoid
            // mis-routing caused by integer/real constant literals.
            if (features.hasMixedIntReal) {
                if (features.hasNonlinear) {
                    atomizer.setDefaultTheory(TheoryId::NIRA);
                    if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
                } else {
                    atomizer.setDefaultTheory(TheoryId::LIRA);
                }
            } else if (features.hasIntVar && features.hasNonlinear) {
                atomizer.setDefaultTheory(TheoryId::NIA);
                if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
            } else if (features.hasIntVar) {
                atomizer.setDefaultTheory(TheoryId::LIA);
            } else if (features.hasRealVar && features.hasNonlinear) {
                atomizer.setDefaultTheory(TheoryId::NRA);
                if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
            } else if (features.hasRealVar) {
                atomizer.setDefaultTheory(TheoryId::LRA);
            } else {
                atomizer.setDefaultTheory(TheoryId::Bool);
            }
        }

        for (ExprId assertion : ir->assertions()) {
            SatLit lit = atomizer.atomize(assertion, *ir);
            sat->addClause({lit});
        }

        // P3: Do NOT eagerly create all shared-term-pair equality atoms.
        // Full arrangement search requires sound theory conflict explanation,
        // complete transitivity handling, and stable model-check replay.
        // Until those are verified, only equalities that appear in the
        // original formula or are explicitly requested by a theory are
        // registered.  UFLIA defaults to Unknown for cases that would need
        // arrangement.
        //
        // if (sharedTermRegistry_) {
        //     const auto& sharedTerms = sharedTermRegistry_->allSharedTerms();
        //     for (size_t i = 0; i < sharedTerms.size(); ++i) {
        //         for (size_t j = i + 1; j < sharedTerms.size(); ++j) {
        //             registry.getOrCreateSharedEqualityAtom(sharedTerms[i], sharedTerms[j]);
        //         }
        //     }
        // }

        if (registry.hasUnsupportedTheoryAtom()) {
            std::cerr << "[Solver] unsupported theory atom detected\n";
            cadicalBackend->disconnectPropagator();
            return Result::Unknown;
        }

        auto result = sat->solve();
        cadicalBackend->disconnectPropagator();

        if (result == SatSolver::SolveResult::Sat) {
            lastModel_ = theoryManager.getModel();
            return Result::Sat;
        }
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

Sort Solver::boolSort() { return Sort{pImpl->getOrCreateBoolSort()}; }
Sort Solver::intSort()  { return Sort{pImpl->getOrCreateIntSort()}; }
Sort Solver::realSort() { return Sort{pImpl->getOrCreateRealSort()}; }
Sort Solver::bvSort(uint32_t) { return Sort{}; /* TODO */ }
Sort Solver::fpSort(uint32_t, uint32_t) { return Sort{}; /* TODO */ }

Term Solver::mkConst(Sort s, std::string_view name) {
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = s.id();
    e.payload = Payload(std::string(name));
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkVar(Sort s, std::string_view name) {
    // In CoreIr, variables and constants both use Kind::Variable.
    return mkConst(s, name);
}

Term Solver::mkBool(bool v) {
    CoreExpr e;
    e.kind = Kind::ConstBool;
    e.sort = pImpl->getOrCreateBoolSort();
    e.payload = Payload(v);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = pImpl->getOrCreateIntSort();
    e.payload = Payload(v);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkReal(const std::string& rational) {
    CoreExpr e;
    e.kind = Kind::ConstReal;
    e.sort = pImpl->getOrCreateRealSort();
    e.payload = Payload(rational);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkOp(uint32_t kind, std::vector<Term> args) {
    CoreExpr e;
    e.kind = static_cast<Kind>(kind);
    // Simple sort inference: for arithmetic ops, take sort from first arg;
    // for boolean ops (And, Or, etc.), use bool sort;
    // for comparisons (Eq, Lt, etc.), use bool sort.
    if (args.empty()) {
        e.sort = NullSort;
    } else if (e.kind == Kind::And || e.kind == Kind::Or || e.kind == Kind::Not ||
               e.kind == Kind::Implies || e.kind == Kind::Xor ||
               e.kind == Kind::Eq || e.kind == Kind::Distinct ||
               e.kind == Kind::Lt || e.kind == Kind::Leq ||
               e.kind == Kind::Gt || e.kind == Kind::Geq) {
        e.sort = pImpl->getOrCreateBoolSort();
    } else {
        // Use the sort of the first argument if IR is available.
        if (pImpl->ir) {
            e.sort = pImpl->ir->get(args[0].id()).sort;
        } else {
            e.sort = NullSort;
        }
    }
    for (const auto& a : args) {
        e.children.push_back(a.id());
    }
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

void Solver::assertFormula(Term t) {
    pImpl->ensureIr().addAssertion(t.id());
}

Result Solver::checkSat() {
    return pImpl->checkSatInternal();
}

Result Solver::checkSatAssuming(std::vector<Term> assumptions) {
    pImpl->lastAssumptions_ = assumptions;
    push();
    for (Term a : assumptions) {
        assertFormula(a);
    }
    Result r = checkSat();
    pop();
    return r;
}

Model Solver::getModel() const {
    Model model;
    if (!pImpl) return model;

    if (!pImpl->lastModel_) return model;

    const auto& theoryModel = *pImpl->lastModel_;

    // Map variable names to ExprIds from CoreIr
    if (pImpl->ir) {
        for (ExprId id = 0; id < static_cast<ExprId>(pImpl->ir->size()); ++id) {
            const auto& expr = pImpl->ir->get(id);
            if (expr.kind != Kind::Variable) continue;
            if (!std::holds_alternative<std::string>(expr.payload.value)) continue;
            const std::string& name = std::get<std::string>(expr.payload.value);
            auto it = theoryModel.assignments.find(name);
            if (it != theoryModel.assignments.end()) {
                model.setValue(id, it->second);
            }
        }
    }

    return model;
}
Term Solver::getValue(Term t) {
    if (!pImpl || !pImpl->ir) return Term{};
    Model m = getModel();
    const std::string* val = m.getValue(t.id());
    if (!val) return Term{};

    const auto& expr = pImpl->ir->get(t.id());
    auto sortKind = pImpl->ir->sortKind(expr.sort);

    if (sortKind == SortKind::Int) {
        int64_t v = std::stoll(*val);
        return mkInt(v);
    } else if (sortKind == SortKind::Real) {
        return mkReal(*val);
    } else if (sortKind == SortKind::Bool) {
        return mkBool(*val == "true");
    }
    return Term{};
}
std::vector<Term> Solver::getUnsatCore() const {
    // TODO: proper unsat core extraction using SAT solver assumptions.
    // For now, return the last assumptions passed to checkSatAssuming.
    if (!pImpl) return {};
    return pImpl->lastAssumptions_;
}
Proof Solver::getProof() const { return Proof{}; }
Statistics Solver::getStatistics() const { return Statistics{}; }

void Solver::dumpSMT2(std::ostream& os) {
    if (pImpl->parser && !pImpl->parser->getAssertions().empty()) {
        for (auto& a : pImpl->parser->getAssertions()) {
            os << SOMTParser::dumpSMTLIB2(a) << "\n";
        }
    } else if (pImpl->ir) {
        for (ExprId aid : pImpl->ir->assertions()) {
            os << dumpExprToSMT2(aid, *pImpl->ir) << "\n";
        }
    }
}

} // namespace nlcolver
