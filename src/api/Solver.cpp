#include "nlcolver/Solver.h"
#include "nlcolver/Result.h"
#include "expr/ir.h"
#include "expr/CoreIteLowerer.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/LinearToIntPurifier.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "expr/Smt2Dumper.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "frontend/atomization/Atomizer.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "frontend/factory/TheoryFactory.h"
#include "theory/core/LogicFeatureDetector.h"
#ifdef NLCOLVER_ENABLE_CASESTATS
#ifdef NLCOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif
#endif

#ifdef NLCOLVER_HAS_CADICAL
#include "sat/CadicalBackend.h"
#include "sat/CadicalTheoryPropagator.h"
#endif

#include <somtparser/frontend/parser.h>

#include <iostream>
#include <unordered_map>
#include <chrono>

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
    std::string lastUnknownReason_;
    std::string lastUnknownCode_;
    std::string lastUnknownComponent_;
    std::string lastUnknownDetail_;

#ifdef NLCOLVER_ENABLE_CASESTATS
    void parseUnknownReasonIntoStats() {
        // Derive structured unknown fields from the free-text reason.
        const std::string& r = lastUnknownReason_;
        if (r.empty()) return;

        // Component detection from prefix
        auto colonPos = r.find(':');
        std::string prefix = (colonPos != std::string::npos) ? r.substr(0, colonPos) : r;

        if (prefix == "IntDivModLowerer") {
            lastUnknownComponent_ = "IntDivModLowerer";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_DIVMOD";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "LinearToIntPurifier") {
            lastUnknownComponent_ = "LinearToIntPurifier";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_TO_INT";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "LogicFeatureDetector") {
            lastUnknownComponent_ = "LogicFeatureDetector";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_FEATURE";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "Atomizer") {
            lastUnknownComponent_ = "Atomizer";
            lastUnknownCode_ = "ATOMIZER_UNSUPPORTED";
            caseStats_.failureStage = "atomizer";
        } else if (prefix == "TheoryFactory") {
            lastUnknownComponent_ = "TheoryFactory";
            lastUnknownCode_ = "FRONTEND_LOGIC_MISMATCH";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "SAT") {
            lastUnknownComponent_ = "SAT";
            lastUnknownCode_ = "SAT_ABORT";
            caseStats_.failureStage = "sat";
        } else if (prefix == "Theory") {
            lastUnknownComponent_ = "Theory";
            lastUnknownCode_ = "THEORY_UNKNOWN";
            caseStats_.failureStage = "theory";
        } else {
            lastUnknownComponent_ = "Unknown";
            lastUnknownCode_ = "UNKNOWN";
            caseStats_.failureStage = "unknown";
        }
        lastUnknownDetail_ = r;
    }

    void finalizeCaseStats(Result result, double timeMs,
                           const CadicalTheoryPropagator* propagator = nullptr,
                           const TheoryManager* theoryManager = nullptr,
                           const CadicalBackend* cadicalBackend = nullptr,
                           const Atomizer* atomizer = nullptr,
                           const TheoryAtomRegistry* registry = nullptr) {
        caseStats_.timeMs = timeMs;
        caseStats_.result = (result == Result::Sat) ? "sat" :
                            (result == Result::Unsat) ? "unsat" :
                            (result == Result::Unknown) ? "unknown" : "error";
        if (result == Result::Unknown) {
            parseUnknownReasonIntoStats();
            caseStats_.unknownCode = lastUnknownCode_;
            caseStats_.unknownComponent = lastUnknownComponent_;
            caseStats_.unknownDetail = lastUnknownDetail_;
        }
        if (theoryManager) {
            caseStats_.activeTheories = theoryManager->activeTheoryNames();
        }
        caseStats_.enabledStats = {"frontend", "sat", "theory", "search"};

        // Frontend stats
        if (atomizer) {
            const auto& atoms = atomizer->atoms();
            caseStats_.frontend.numAtoms = static_cast<int64_t>(atoms.size());
            int64_t boolAtoms = 0, arithAtoms = 0, eufAtoms = 0;
            for (const auto& a : atoms) {
                if (a.isTheory) {
                    switch (a.theory) {
                        case TheoryId::EUF: ++eufAtoms; break;
                        case TheoryId::LRA:
                        case TheoryId::LIA:
                        case TheoryId::NRA:
                        case TheoryId::NIA:
                        case TheoryId::IDL:
                        case TheoryId::RDL:
                        case TheoryId::LIRA:
                        case TheoryId::NIRA:
                        case TheoryId::Combination:
                            ++arithAtoms; break;
                        default: break;
                    }
                } else {
                    ++boolAtoms;
                }
            }
            caseStats_.frontend.numBoolAtoms = boolAtoms;
            caseStats_.frontend.numArithAtoms = arithAtoms;
            caseStats_.frontend.numEufAtoms = eufAtoms;
        }
        if (registry) {
            caseStats_.frontend.numUnsupported = registry->hasUnsupportedTheoryAtom() ? 1 : 0;
        }
        if (ir) {
            caseStats_.frontend.numExpr = static_cast<int64_t>(ir->assertions().size());
        }

        // SAT stats
        if (cadicalBackend) {
            auto satStats = cadicalBackend->getStats();
            caseStats_.sat.vars = satStats.vars;
            caseStats_.sat.clauses = satStats.clauses;
            caseStats_.sat.conflicts = satStats.conflicts;
            caseStats_.sat.decisions = satStats.decisions;
            caseStats_.sat.propagations = satStats.propagations;
        }

        // Theory stats
        if (theoryManager) {
            const auto& agg = theoryManager->aggregateStats();
            caseStats_.theory.checkCalls = agg.checkCalls;
            caseStats_.theory.conflicts = agg.conflicts;
            caseStats_.theory.lemmas = agg.lemmas;
            caseStats_.theory.propagations = agg.propagations;
            if (agg.conflicts > 0) {
                caseStats_.theory.avgConflictSize = static_cast<double>(agg.totalConflictSize) / agg.conflicts;
            }
            caseStats_.theory.maxConflictSize = agg.maxConflictSize;
        }

        // Search stats (from propagator)
        if (propagator) {
            const auto& ps = propagator->stats();
            caseStats_.search.modelCheckCalls = ps.modelCheckCount;
            caseStats_.search.modelCheckConflicts = ps.modelCheckConflict;
            caseStats_.search.modelCheckLemmas = ps.modelCheckLemma;
            caseStats_.search.modelCheckUnknowns = ps.modelCheckUnknown;

            int totalConflicts = ps.modelCheckConflict + ps.propagateConflictCount;
            long long totalConflictSize = ps.conflictTotalSize + ps.propagateConflictTotalSize;
            caseStats_.search.conflictMinSize = ps.conflictMinSize;
            if (ps.propagateConflictCount > 0) {
                if (caseStats_.search.conflictMinSize < 0 ||
                    ps.propagateConflictMinSize < caseStats_.search.conflictMinSize) {
                    caseStats_.search.conflictMinSize = ps.propagateConflictMinSize;
                }
            }
            caseStats_.search.conflictMaxSize = std::max(ps.conflictMaxSize, ps.propagateConflictMaxSize);
            if (totalConflicts > 0) {
                caseStats_.search.conflictAvgSize = static_cast<double>(totalConflictSize) / totalConflicts;
            }
            caseStats_.search.propagateCalls = ps.propagateCallCount;
            caseStats_.search.propagateTheoryChecks = ps.propagateTheoryCheckCount;
            caseStats_.search.propagateConflicts = ps.propagateConflictCount;
            caseStats_.search.propagateLemmas = ps.propagateLemmaCount;
        }

        if (!dumpStatsPath_.empty()) {
            caseStats_.dumpToFile(dumpStatsPath_);
        }
    }
#endif
#ifdef NLCOLVER_ENABLE_CASESTATS
    CaseStats caseStats_;
    std::string dumpStatsPath_;
#endif

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
        lastAssumptions_.clear();
        lastUnknownReason_.clear();
        lastUnknownCode_.clear();
        lastUnknownComponent_.clear();
        lastUnknownDetail_.clear();
#ifdef NLCOLVER_ENABLE_CASESTATS
        caseStats_ = CaseStats{};
#endif
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
        lastUnknownReason_.clear();
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

        // Lower integer div/mod before arithmetic extraction.
        {
            IntDivModLowerer dmLowerer(*ir);
            if (!dmLowerer.run()) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported or internal error";
#ifdef NLCOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            const auto& req = dmLowerer.requirement();
            bool hasEuf = (logic == "QF_UF" || logic == "QF_UFLRA" || logic == "QF_UFLIA" ||
                           logic == "QF_UFNIA" || logic == "UFNIA" ||
                           logic == "QF_UFNRA" || logic == "UFNRA");
            bool isLinearOnly = (logic == "QF_LIA" || logic == "LIA" ||
                                 logic == "QF_LIRA" || logic == "LIRA" ||
                                 logic == "QF_IDL" || logic == "IDL" ||
                                 logic == "QF_RDL" || logic == "RDL" ||
                                 logic == "QF_UFLIA" || logic == "UFLIA" ||
                                 logic == "QF_UFLRA" || logic == "UFLRA");
            if (req.unsupported) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported divisor";
#ifdef NLCOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            if (req.needsEUF && !hasEuf) {
                lastUnknownReason_ = "IntDivModLowerer: needsEUF but logic=" + logic;
#ifdef NLCOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            if (req.needsNonlinearInt && isLinearOnly) {
                lastUnknownReason_ = "IntDivModLowerer: needsNonlinearInt but logic=" + logic;
#ifdef NLCOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            dmLowerer.commit();
        }

        // Normalize arithmetic casts (fold constant to_int/to_real)
        {
            ArithCastNormalizer normalizer(*ir);
            auto normResult = normalizer.run();
            ir->clearAssertions();
            for (const auto& [level, a] : normResult.assertions) {
                ir->addAssertion(a, level);
            }
        }

        // Purify linear to_int applications into fresh Int variables + floor lemmas
        {
            LinearToIntPurifier purifier(*ir);
            auto detectResult = purifier.detectOnly();
            if (detectResult.hasUnsupportedNonlinearToInt) {
                lastUnknownReason_ = "LinearToIntPurifier: unsupported nonlinear to_int";
#ifdef NLCOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            auto purifyResult = purifier.run();
            ir->clearAssertions();
            for (const auto& [level, a] : purifyResult.purifiedAssertions) {
                ir->addAssertion(a, level);
            }
            for (const auto& [level, lemma] : purifyResult.floorLemmas) {
                ir->addAssertion(lemma, level);
            }
        }

        // Apply solver options (seed, etc.)
        auto itSeed = options.find("seed");
        if (itSeed != options.end() && itSeed->second.kind == OptionValue::Int) {
            sat->configure("seed", itSeed->second.i);
        }

#ifndef NLCOLVER_HAS_CADICAL
        lastUnknownReason_ = "SAT: CaDiCaL backend not compiled";
#ifdef NLCOLVER_ENABLE_CASESTATS
        finalizeCaseStats(Result::Unknown, 0.0);
#endif
        return Result::Unknown;
#else
        auto* cadicalBackend = dynamic_cast<CadicalBackend*>(sat.get());
        if (!cadicalBackend) {
            lastUnknownReason_ = "SAT: CadicalBackend cast failed";
#ifdef NLCOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0);
#endif
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
            lastUnknownReason_ = "LogicFeatureDetector: logic mismatch (declared=" + logic + ")";
#ifdef NLCOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        if (features.hasUnsupported) {
            lastUnknownReason_ = "LogicFeatureDetector: unsupported feature (quantifier/array/FP/BV)";
#ifdef NLCOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // -------------------------------------------------------------------
        // Register solvers based on logic or detected features
        // -------------------------------------------------------------------
        auto setupResult = setupSolvers(
            logic, features, ir.get(), registry, theoryManager,
            sharedTermRegistry_, boolSortId_);

        if (!setupResult.success) {
            lastUnknownReason_ = "TheoryFactory: solver setup failed (unsupported logic=" + logic + ")";
#ifdef NLCOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }
        if (setupResult.logicMismatch) {
            lastUnknownReason_ = "TheoryFactory: logic mismatch in setupSolvers";
            logicMismatch = true;
        }
        polyKernelRaw = setupResult.polyKernelRaw;

        // Connect propagator FIRST (required before addObservedVar)
        CadicalTheoryPropagator propagator(registry, theoryManager, lemmaDb, *cadicalBackend);
        propagator.setUnknownReasonSink(&lastUnknownReason_);
#ifdef NLCOLVER_ENABLE_CASESTATS
        propagator.setCaseStats(&caseStats_);
        if (!dumpStatsPath_.empty()) {
            // Base path without extension for heartbeat
            propagator.setDumpStatsBasePath(dumpStatsPath_);
        }
#endif
        cadicalBackend->connectPropagator(&propagator);

        // Atomizer registers parsed atoms into registry (which calls addObservedVar)
        Atomizer atomizer(*sat);
        registry.setContext(sat.get(), &atomizer);
        atomizer.setRegistry(&registry);
        atomizer.setBoolSortId(boolSortId_);

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
        } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
        } else if (logic == "QF_UFLIA" || logic == "UFLIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::LIA);
        } else if (logic == "QF_UFNIA" || logic == "UFNIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::NIA);
            if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
        } else if (logic == "QF_UFNRA" || logic == "UFNRA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::NRA);
            if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
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
            lastUnknownReason_ = "Atomizer: unsupported theory atom";
#ifdef NLCOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, &theoryManager,
                              cadicalBackend, &atomizer, &registry);
#endif
            cadicalBackend->disconnectPropagator();
            return Result::Unknown;
        }

        auto solveT0 = std::chrono::steady_clock::now();
        auto result = sat->solve();
        auto solveT1 = std::chrono::steady_clock::now();
        auto solveDurMs = std::chrono::duration_cast<std::chrono::microseconds>(solveT1 - solveT0).count() / 1000.0;
        cadicalBackend->disconnectPropagator();
        propagator.stats().print(std::cerr);

        Result ret = Result::Unknown;
        if (result == SatSolver::SolveResult::Sat) {
            lastModel_ = theoryManager.getModel();
            ret = Result::Sat;
        } else if (result == SatSolver::SolveResult::Unsat) {
            ret = Result::Unsat;
        } else {
            if (lastUnknownReason_.empty()) {
                lastUnknownReason_ = "SAT: solve returned Unknown (propagator abort or timeout)";
            }
            ret = Result::Unknown;
        }

#ifdef NLCOLVER_ENABLE_CASESTATS
        finalizeCaseStats(ret, solveDurMs, &propagator, &theoryManager,
                          cadicalBackend, &atomizer, &registry);
#endif
        return ret;
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

std::string Solver::lastUnknownReason() const { return pImpl->lastUnknownReason_; }
std::string Solver::lastUnknownCode() const { return pImpl->lastUnknownCode_; }
std::string Solver::lastUnknownComponent() const { return pImpl->lastUnknownComponent_; }
std::string Solver::lastUnknownDetail() const { return pImpl->lastUnknownDetail_; }

#ifdef NLCOLVER_ENABLE_CASESTATS
void Solver::setDumpStatsPath(std::string_view path) {
    pImpl->dumpStatsPath_ = std::string(path);
}
#else
void Solver::setDumpStatsPath(std::string_view) {}
#endif

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
