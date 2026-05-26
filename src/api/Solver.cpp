#include "zolver/Solver.h"
#include "zolver/Result.h"
#include "expr/ir.h"
#include "expr/CoreIteLowerer.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/BoolSubtermPurifier.h"
#include "frontend/preprocess/UfInArithPurifier.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include "frontend/preprocess/IntDivModConstantFold.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "frontend/preprocess/ModularConsistencyChecker.h"
#include "frontend/preprocess/NaryDistinctLowerer.h"
#include "frontend/preprocess/ToRealLiteralFold.h"
#include "frontend/preprocess/UnconditionalConstantPropagation.h"
#include "theory/arith/search/CandidateModelSearch.h"
#include "proof/ArithModelValidator.h"
#include <gmpxx.h>
#include "expr/Smt2Dumper.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "frontend/atomization/Atomizer.h"
#include "theory/core/TheoryManager.h"
#include "theory/arith/linear/BoundAxiomGenerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "frontend/factory/TheoryFactory.h"
#include "theory/core/LogicFeatureDetector.h"
#ifdef ZOLVER_ENABLE_CASESTATS
#ifdef ZOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif
#endif

#include "sat/CadicalBackend.h"
#include "sat/CadicalTheoryPropagator.h"

#include <somtparser/frontend/parser.h>

#include <iostream>
#include <sstream>
#include <set>
#include <unordered_map>
#include <map>
#include <functional>
#include <optional>
#include <chrono>

namespace zolver {

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
    // Original (pre-lowering) assertion roots, snapshotted each checkSat for
    // the independent model self-check (modelMatchesOriginal).
    std::vector<ExprId> originalAssertions_;

    // Partial-function (div/mod-by-zero) model support. divModOrigins_ is
    // captured from IntDivModLowerer; partialFuncModel_ is the chosen total
    // extension at undefined inputs, built from the final model (see
    // buildPartialFuncModel) and emitted as define-fun shadows in dumpModel.
    std::vector<DivModOrigin> divModOrigins_;
    struct PartialFuncModel {
        std::map<mpq_class, mpq_class> divZero;  // a -> chosen (div a 0)
        std::map<mpq_class, mpq_class> modZero;  // a -> chosen (mod a 0)
        bool inconsistent = false;   // same input -> two outputs (safety net)
        bool realDivByZero = false;  // a Real `/` had a 0 denominator (round-1 gate)
    };
    PartialFuncModel partialFuncModel_;

    std::string lastUnknownReason_;
    std::string lastUnknownCode_;
    std::string lastUnknownComponent_;
    std::string lastUnknownDetail_;

    // True iff the SMT-LIB input set :produce-models / issued (get-model).
    bool modelRequestedImpl() const {
        if (!parser) return false;
        auto opts = parser->getOptions();
        return opts && opts->get_model;
    }

    // True only on a DEFINITE violation of an original (pre-lowering)
    // assertion by the current lastModel_ (mirrors the negation of
    // Solver::modelMatchesOriginal). Drives the validated model-repair.
    bool modelViolatesOriginal() const {
        if (!ir || !lastModel_) return false;
        ArithModelValidator::NumAssignment numAsg;
        ArithModelValidator::BoolAssignment boolAsg;
        for (const auto& [name, val] : lastModel_->assignments) {
            if (val == "true")  { boolAsg[name] = true;  continue; }
            if (val == "false") { boolAsg[name] = false; continue; }
            try { numAsg[name] = mpq_class(val); } catch (...) {}
        }
        ArithModelValidator validator(*ir, numAsg, boolAsg);
        return validator.validate(originalAssertions_)
               == ArithModelValidator::Verdict::Violated;
    }

    // QF_AX: re-validate the extracted array model against the ORIGINAL
    // assertions. Returns true only if the model is present and the validator
    // does NOT report a definite violation. A missing model or an
    // Indeterminate result is treated as "cannot confirm" → false (gate to
    // Unknown), so we never emit an unvalidated array sat.
    bool arrayModelValidates() const {
        if (!ir || !lastModel_) return false;
        if (lastModel_->arrayInterps.empty()) return false;  // nothing to stand on

        // QF_AX is arithmetic-free: index/element vars are opaque tokens, so we
        // route EVERY scalar variable through the token channel (already in the
        // validator's canonical namespaced form, as emitted by getModel) and
        // leave numAsg empty. Bool vars go through both channels.
        //
        // For the COMBINATION array logics (QF_ALIA/ALRA/AUFLIA/AUFLRA) the
        // index/element values are concrete NUMBERS coming from the arith
        // model: getModel() coerces them to "#n:<rational>" tokens (so they
        // compare equal to a number's token inside an array interp). We
        // additionally peel "#n:" back into numAsg so arithmetic atoms like
        // (> i 5) evaluate to a definite truth value rather than Indeterminate.
        ArithModelValidator::NumAssignment numAsg;
        ArithModelValidator::BoolAssignment boolAsg;
        ArithModelValidator::TokenAssignment tokAsg;
        for (const auto& [name, val] : lastModel_->assignments) {
            if (val == "true")  { boolAsg[name] = true;  tokAsg[name] = "#b:1"; continue; }
            if (val == "false") { boolAsg[name] = false; tokAsg[name] = "#b:0"; continue; }
            tokAsg[name] = val;  // canonical token from getModel
            if (val.rfind("#n:", 0) == 0) {
                try { numAsg[name] = mpq_class(val.substr(3)); } catch (...) {}
            } else {
                // Bare numeric (defensive: some paths may not namespace).
                try { numAsg[name] = mpq_class(val); } catch (...) {}
            }
        }
        ArithModelValidator validator(*ir, numAsg, boolAsg,
                                      lastModel_->arrayInterps, tokAsg);
        return validator.validate(originalAssertions_)
               != ArithModelValidator::Verdict::Violated;
    }

    // Array SAT soundness safety net (ALL tracks, incl. Single-Query). Builds
    // the array model internally and runs ArithModelValidator over the ORIGINAL
    // assertions, returning true ONLY when the verdict is a DEFINITE Violated.
    // Unlike arrayModelValidates() this is conservative in the SOUND direction:
    //   - a missing model / empty interps / Indeterminate -> false (do NOT
    //     downgrade — never spuriously reject a genuine sat);
    //   - only a definite Violated -> true (downgrade Sat -> Unknown).
    // This guards against a missed Row2/Ext instance escaping as a spurious sat
    // even when no model was requested. It must never fire for a genuinely-sat
    // case (the recently-fixed model construction produces valid store/const
    // models that validate).
    bool arrayModelDefinitelyViolates() const {
        if (!ir || !lastModel_) return false;
        ArithModelValidator::NumAssignment numAsg;
        ArithModelValidator::BoolAssignment boolAsg;
        ArithModelValidator::TokenAssignment tokAsg;
        for (const auto& [name, val] : lastModel_->assignments) {
            if (val == "true")  { boolAsg[name] = true;  tokAsg[name] = "#b:1"; continue; }
            if (val == "false") { boolAsg[name] = false; tokAsg[name] = "#b:0"; continue; }
            tokAsg[name] = val;
            if (val.rfind("#n:", 0) == 0) {
                try { numAsg[name] = mpq_class(val.substr(3)); } catch (...) {}
            } else {
                try { numAsg[name] = mpq_class(val); } catch (...) {}
            }
        }
        ArithModelValidator validator(*ir, numAsg, boolAsg,
                                      lastModel_->arrayInterps, tokAsg);
        return validator.validate(originalAssertions_)
               == ArithModelValidator::Verdict::Violated;
    }

    // Build the partial-function (div/mod-by-zero) model from the final model.
    // For each lowered div/mod whose divisor is 0 under the model, record the
    // chosen result (the value of the fresh quotient q / remainder r) keyed by
    // the dividend value a. A FuncInterp is a function, so re-encountering the
    // same input with a different output signals a model-extraction bug
    // (partialFuncModel_.inconsistent). Also gates Real `/` by a 0 denominator,
    // which round 1 does not emit.
    void buildPartialFuncModel() {
        partialFuncModel_ = PartialFuncModel{};
        if (!ir || !lastModel_) return;
        ArithModelValidator::NumAssignment numAsg;
        ArithModelValidator::BoolAssignment boolAsg;
        for (const auto& [name, val] : lastModel_->assignments) {
            if (val == "true")  { boolAsg[name] = true;  continue; }
            if (val == "false") { boolAsg[name] = false; continue; }
            try { numAsg[name] = mpq_class(val); } catch (...) {}
        }
        // Mirror dumpModel's defaulting of unconstrained user variables (0 /
        // false) so the partial-function table agrees with the printed model:
        // a dividend the theory left unassigned is emitted as 0, so it must
        // evaluate to 0 here too.
        if (parser) {
            for (const auto& var : parser->getDeclaredVariables()) {
                if (!var) continue;
                std::string nm = var->getName();
                if (var->isVBool()) { if (!boolAsg.count(nm)) boolAsg[nm] = false; }
                else if (var->isVInt() || var->isVReal()) {
                    if (!numAsg.count(nm)) numAsg[nm] = mpq_class(0);
                }
            }
        }
        ArithModelValidator validator(*ir, numAsg, boolAsg);

        auto recordInto = [](std::map<mpq_class, mpq_class>& tbl, const mpq_class& in,
                             const mpq_class& out, bool& inconsistent) {
            auto it = tbl.find(in);
            if (it != tbl.end()) { if (it->second != out) inconsistent = true; }
            else tbl.emplace(in, out);
        };

        for (const auto& o : divModOrigins_) {
            auto bv = validator.evalNumber(o.b);
            if (!bv || *bv != 0) continue;          // divisor nonzero under model
            auto av = validator.evalNumber(o.a);
            if (!av) continue;                       // input undetermined -> leave gap
            if (auto qv = validator.evalNumber(o.q))
                recordInto(partialFuncModel_.divZero, *av, *qv, partialFuncModel_.inconsistent);
            if (auto rv = validator.evalNumber(o.r))
                recordInto(partialFuncModel_.modZero, *av, *rv, partialFuncModel_.inconsistent);
        }

        partialFuncModel_.realDivByZero = realDivisionByZeroUnderModel(validator);
    }

    // True iff some Real `/` in the original assertions has a 0 denominator
    // under the model (round-1 gate: such a model is downgraded to Unknown
    // because we do not yet emit a `define-fun /` shadow).
    bool realDivisionByZeroUnderModel(const ArithModelValidator& v) const {
        if (!ir) return false;
        std::unordered_map<ExprId, bool> seen;
        std::function<bool(ExprId)> walk = [&](ExprId e) -> bool {
            if (e == NullExpr || e >= ir->size()) return false;
            if (!seen.emplace(e, true).second) return false;
            const CoreExpr& n = ir->get(e);
            if (n.kind == Kind::Div && n.children.size() == 2 &&
                ir->sortKind(n.sort) == SortKind::Real) {
                if (auto d = v.evalNumber(n.children[1])) if (*d == 0) return true;
            }
            for (ExprId c : n.children) if (walk(c)) return true;
            return false;
        };
        for (ExprId a : originalAssertions_) if (walk(a)) return true;
        return false;
    }

#ifdef ZOLVER_ENABLE_CASESTATS
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
        } else if (prefix == "ToIntDefinitionalLowerer") {
            lastUnknownComponent_ = "ToIntDefinitionalLowerer";
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
#ifdef ZOLVER_ENABLE_CASESTATS
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
        originalAssertions_.clear();
        divModOrigins_.clear();
        partialFuncModel_ = PartialFuncModel{};
        lastUnknownReason_.clear();
        lastUnknownCode_.clear();
        lastUnknownComponent_.clear();
        lastUnknownDetail_.clear();
#ifdef ZOLVER_ENABLE_CASESTATS
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
        // Propagate the Bool sort id into the CoreIr now, before any
        // preprocessing pass creates Bool-sorted variables. Otherwise
        // ir->boolSortId() stays NullSort (getOrCreateBoolSort short-circuits
        // when the Solver member is already set, skipping cir.setBoolSortId),
        // so BoolSubtermPurifier creates `boolpur` vars with NullSort. The
        // Atomizer then fails to recognize those vars as Boolean and routes
        // boolean (= / distinct) iffs over them into the arithmetic theory as
        // difference (dis)equalities — an unbounded relaxation that yields
        // unsound SAT in QF_IDL/QF_LIA (Averest false-SAT cluster).
        if (boolSortId_ != NullSort) {
            ir->setBoolSortId(boolSortId_);
        }
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

        // Snapshot the ORIGINAL (pre-lowering) assertion roots for the
        // independent model self-check (modelMatchesOriginal). Lowering
        // passes only APPEND CoreExpr nodes (CoreIr::add never mutates), so
        // these ExprIds keep referencing the original formula even after
        // the assertion list is rewritten by lowering.
        originalAssertions_ = ir->assertions();

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

        // Cap. 8a — UnconditionalConstantPropagation.
        // Collect (= var ConstNumeric) from top-level unconditional
        // conjuncts; substitute the variable by the constant globally
        // (including under ite / or / => / mod / div / to_real / to_int).
        // This is sound: an unconditional binding holds in every model.
        // On contradictory bindings the Solver short-circuits to UNSAT.
        {
            UnconditionalConstantPropagation cprop(*ir);
            cprop.run();
            if (cprop.hadContradiction()) {
#ifdef ZOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unsat, 0.0);
#endif
                return Result::Unsat;
            }
            cprop.commit();
        }

        // Cap. 8b — ToRealLiteralFold.
        // Pure constant folding: (to_real ConstInt k) -> ConstReal k,
        // (to_real ConstReal r) unwrapped, and (/ ConstReal a ConstReal b)
        // folded to ConstReal (a/b) when b != 0. Runs after Cap. 8a so
        // it sees the constant-propagated to_real arguments.
        {
            ToRealLiteralFold fold(*ir);
            fold.run();
            fold.commit();
        }

        // CRT consistency check for (= (mod x N) c) patterns BEFORE lowering.
        // Closes UNSAT cases by direct contradiction and pins SAT cases with
        // a unique witness in a finite bound. Mod patterns hidden inside
        // boolean composites are deferred to the standard pipeline.
        {
            ModularConsistencyChecker crt(*ir);
            crt.run();
        }

        // Cap. 8e' — IntDivModConstantFold.
        // Fold (div ConstInt a ConstInt b) and (mod ConstInt a ConstInt b)
        // to literal ConstInt results under SMT-LIB integer-division
        // semantics. Runs BEFORE IntDivModLowerer so that constant-only
        // div/mod do not allocate fresh quotient/remainder variables.
        {
            IntDivModConstantFold dmFold(*ir);
            dmFold.run();
            dmFold.commit();
        }

        // Lower integer div/mod before arithmetic extraction.
        {
            IntDivModLowerer dmLowerer(*ir);
            if (!dmLowerer.run()) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported or internal error";
#ifdef ZOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            const auto& req = dmLowerer.requirement();
            bool hasEuf = (logic == "QF_UF" || logic == "QF_UFLRA" || logic == "QF_UFLIA" ||
                           logic == "QF_UFNIA" || logic == "UFNIA" ||
                           logic == "QF_UFNRA" || logic == "UFNRA" ||
                           logic == "QF_AX" ||
                           logic == "QF_ALIA" || logic == "ALIA" ||
                           logic == "QF_ALRA" || logic == "ALRA" ||
                           logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                           logic == "QF_AUFLRA" || logic == "AUFLRA");
            bool isLinearOnly = (logic == "QF_LIA" || logic == "LIA" ||
                                 logic == "QF_LIRA" || logic == "LIRA" ||
                                 logic == "QF_IDL" || logic == "IDL" ||
                                 logic == "QF_RDL" || logic == "RDL" ||
                                 logic == "QF_UFLIA" || logic == "UFLIA" ||
                                 logic == "QF_UFLRA" || logic == "UFLRA" ||
                                 logic == "QF_ALIA" || logic == "ALIA" ||
                                 logic == "QF_ALRA" || logic == "ALRA" ||
                                 logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                                 logic == "QF_AUFLRA" || logic == "AUFLRA");
            if (req.unsupported) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported divisor";
#ifdef ZOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            if (req.needsEUF && !hasEuf) {
                lastUnknownReason_ = "IntDivModLowerer: needsEUF but logic=" + logic;
#ifdef ZOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            if (req.needsNonlinearInt && isLinearOnly) {
                lastUnknownReason_ = "IntDivModLowerer: needsNonlinearInt but logic=" + logic;
#ifdef ZOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            dmLowerer.commit();
            // Retain div/mod origins so the model dump can emit define-fun
            // shadows giving our chosen value at undefined (divisor-0) inputs.
            divModOrigins_ = dmLowerer.origins();
        }

        // Lower n-ary distinct to pairwise binary distinct
        {
            NaryDistinctLowerer distinctLowerer(*ir);
            distinctLowerer.run();
            distinctLowerer.commit();
        }

        // Purify boolean composites in argument positions
        {
            BoolSubtermPurifier boolPurifier(*ir);
            boolPurifier.run();
            boolPurifier.commit();
        }

        // Bridge UF applications inside arithmetic expressions
        {
            UfInArithPurifier ufPurifier(*ir);
            ufPurifier.run();
            ufPurifier.commit();
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

        // Cap. 8c — ToIntDefinitionalLowerer (replaces LinearToIntPurifier).
        // Lowers every (to_int t) into fresh Int i_t and fresh Real r_t,
        // emitting (= r_t t) plus the floor sandwich
        //   (<= (to_real i_t) r_t)  and  (< r_t (+ (to_real i_t) 1)).
        // Unlike LinearToIntPurifier this pass succeeds on NONLINEAR `t`;
        // the bridge equality is routed to NRA/NIRA by the atomizer. If
        // the introduced bridges are nonlinear, the declared logic is
        // upgraded (QF_LIA -> QF_NIA, QF_LRA -> QF_NRA, QF_LIRA -> QF_NIRA,
        // etc.) so the LogicFeatureDetector mismatch guard does not fire.
        {
            ToIntDefinitionalLowerer t2i(*ir);
            t2i.run();
            t2i.commit();

            if (t2i.hadNonlinearBridge()) {
                // Upgrade declared logic to the nonlinear counterpart.
                // The new bridge equality `r_t = nonlinear_t` cannot be
                // handled by a linear theory, so we widen the theory scope.
                // NIRA subsumes NIA/NRA/LIA/LRA/LIRA. Any logic that
                // already permits nonlinear (NRA/NIA/NIRA) stays unchanged.
                auto upgrade = [](const std::string& l) -> std::string {
                    if (l == "QF_LIA")   return "QF_NIA";
                    if (l == "LIA")      return "NIA";
                    if (l == "QF_LRA")   return "QF_NRA";
                    if (l == "LRA")      return "NRA";
                    if (l == "QF_LIRA")  return "QF_NIRA";
                    if (l == "LIRA")     return "NIRA";
                    if (l == "QF_UFLIA") return "QF_UFNIA";
                    if (l == "UFLIA")    return "UFNIA";
                    if (l == "QF_UFLRA") return "QF_UFNRA";
                    if (l == "UFLRA")    return "UFNRA";
                    return l;
                };
                logic = upgrade(logic);
            } else if (t2i.hadIntBridge() && t2i.hadRealBridge()) {
                // Bridge is linear but mixed Int/Real: widen pure-Real or
                // pure-Int linear logics to the mixed LIRA family.
                auto upgrade = [](const std::string& l) -> std::string {
                    if (l == "QF_LRA")  return "QF_LIRA";
                    if (l == "LRA")     return "LIRA";
                    if (l == "QF_LIA")  return "QF_LIRA";
                    if (l == "LIA")     return "LIRA";
                    if (l == "QF_NRA")  return "QF_NIRA";
                    if (l == "NRA")     return "NIRA";
                    if (l == "QF_NIA")  return "QF_NIRA";
                    if (l == "NIA")     return "NIRA";
                    return l;
                };
                logic = upgrade(logic);
            }
        }

        // Apply solver options (seed, etc.)
        auto itSeed = options.find("seed");
        if (itSeed != options.end() && itSeed->second.kind == OptionValue::Int) {
            sat->configure("seed", itSeed->second.i);
        }


        auto* cadicalBackend = dynamic_cast<CadicalBackend*>(sat.get());
        if (!cadicalBackend) {
            lastUnknownReason_ = "SAT: CadicalBackend cast failed";
#ifdef ZOLVER_ENABLE_CASESTATS
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
            if (features.hasInterpretedArithmetic) logicMismatch = true;
        } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
            if (features.hasIntVar || features.hasMixedIntReal) logicMismatch = true;
        } else if (logic == "QF_LIRA" || logic == "LIRA") {
            if (features.hasNonlinear || features.hasUF) logicMismatch = true;
        } else if (logic == "QF_NIRA" || logic == "NIRA") {
            if (features.hasUF) logicMismatch = true;
        } else if (logic == "QF_ALIA" || logic == "ALIA") {
            if (features.hasRealVar || features.hasMixedIntReal ||
                features.hasNonlinear || features.hasUF) logicMismatch = true;
        } else if (logic == "QF_ALRA" || logic == "ALRA") {
            if (features.hasIntVar || features.hasMixedIntReal ||
                features.hasNonlinear || features.hasUF) logicMismatch = true;
        } else if (logic == "QF_AUFLIA" || logic == "AUFLIA") {
            if (features.hasRealVar || features.hasMixedIntReal ||
                features.hasNonlinear) logicMismatch = true;
        } else if (logic == "QF_AUFLRA" || logic == "AUFLRA") {
            if (features.hasIntVar || features.hasMixedIntReal ||
                features.hasNonlinear) logicMismatch = true;
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
#ifdef ZOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        if (features.hasUnsupported) {
            lastUnknownReason_ = "LogicFeatureDetector: unsupported feature (quantifier/FP/BV)";
#ifdef ZOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // Arrays are only handled by the array logics: pure QF_AX and the
        // combination logics QF_ALIA/QF_ALRA/QF_AUFLIA/QF_AUFLRA. Any other
        // logic that contains arrays is gated to Unknown (sound).
        auto isArrayLogic = [](const std::string& l) {
            return l == "QF_AX" ||
                   l == "QF_ALIA" || l == "ALIA" ||
                   l == "QF_ALRA" || l == "ALRA" ||
                   l == "QF_AUFLIA" || l == "AUFLIA" ||
                   l == "QF_AUFLRA" || l == "AUFLRA";
        };
        if (features.hasArray && !isArrayLogic(logic)) {
            lastUnknownReason_ = "LogicFeatureDetector: array feature outside array logic (declared=" + logic + ")";
#ifdef ZOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // -------------------------------------------------------------------
        // Register solvers based on logic or detected features
        // -------------------------------------------------------------------
        bool liaSafeMode = false;
        bool liaUltraSafeMode = false;
        bool liaEnableSingleVar = false;
        bool liaEnableGcdIneq = false;
        bool liaEnableEqGcdNorm = false;
        auto itOpt = options.find("lia-safe-mode");
        if (itOpt != options.end() && itOpt->second.kind == OptionValue::Bool) {
            liaSafeMode = itOpt->second.b;
        }
        itOpt = options.find("lia-ultra-safe-mode");
        if (itOpt != options.end() && itOpt->second.kind == OptionValue::Bool) {
            liaUltraSafeMode = itOpt->second.b;
        }
        itOpt = options.find("lia-enable-single-var-tightening");
        if (itOpt != options.end() && itOpt->second.kind == OptionValue::Bool) {
            liaEnableSingleVar = itOpt->second.b;
        }
        itOpt = options.find("lia-enable-gcd-ineq-tightening");
        if (itOpt != options.end() && itOpt->second.kind == OptionValue::Bool) {
            liaEnableGcdIneq = itOpt->second.b;
        }
        itOpt = options.find("lia-enable-eq-gcd-normalization");
        if (itOpt != options.end() && itOpt->second.kind == OptionValue::Bool) {
            liaEnableEqGcdNorm = itOpt->second.b;
        }

        auto setupResult = setupSolvers(
            logic, features, ir.get(), registry, theoryManager,
            sharedTermRegistry_, boolSortId_,
            liaSafeMode, liaUltraSafeMode,
            liaEnableSingleVar, liaEnableGcdIneq, liaEnableEqGcdNorm);

        if (!setupResult.success) {
            lastUnknownReason_ = "TheoryFactory: solver setup failed (unsupported logic=" + logic + ")";
#ifdef ZOLVER_ENABLE_CASESTATS
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
#ifdef ZOLVER_ENABLE_CASESTATS
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
        } else if (logic == "QF_AX") {
            atomizer.setDefaultTheory(TheoryId::EUF);
        } else if (logic == "QF_ALRA" || logic == "ALRA" ||
                   logic == "QF_AUFLRA" || logic == "AUFLRA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::LRA);
        } else if (logic == "QF_ALIA" || logic == "ALIA" ||
                   logic == "QF_AUFLIA" || logic == "AUFLIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::LIA);
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

        // ZOLVER_LRA_BOUND_AXIOMS (default OFF): emit theory-tautology clauses
        // relating same-form linear bound atoms (e.g. (L<=3)=>(L<=5),
        // ¬((L<=3)∧(L>=5))) so CaDiCaL's BCP propagates bound implications the
        // SAT core can't otherwise see — collapsing the immediate-bound-conflict
        // churn at the root. Branch-independent tautologies: sound by construction.
        BoundAxiomGenerator::generate(registry, *sat);

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
#ifdef ZOLVER_ENABLE_CASESTATS
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
            // NOTE: we intentionally do NOT gate the SAT verdict on
            // re-validating the extracted model against the original
            // assertions. Verdict soundness ("a model exists", derived by
            // the theory) is a separate concern from model-extraction
            // correctness ("our printed model satisfies"). Some paths
            // (Nelson-Oppen combination, parts of NRA/NIRA) currently
            // extract a model that can violate an original assertion even
            // though the SAT verdict is correct; downgrading those to
            // Unknown would discard correct verdicts. `ArithModelValidator`
            // exists to self-check the *printed* model for the
            // Model-Validation track and to back the model-check tool —
            // not to override the verdict. See modelMatchesOriginal().
            //
            // Validated model repair (Model-Validation track only). When a
            // model is requested and the extracted one DEFINITELY violates an
            // original assertion — e.g. Nelson-Oppen combination collapsing
            // a != b, or a NIRA witness whose real root is coupled to an Int
            // via to_int and could not be forwarded — fall back to the
            // SAT-only validated candidate search and adopt its model iff it
            // is found and not itself violated. This never changes the
            // verdict (already Sat); it only replaces a provably-wrong model
            // with a validated one.
            if (modelRequestedImpl() && modelViolatesOriginal()) {
                // Search over the ORIGINAL assertions, not the lowered IR:
                // lowering introduces __nlc_ auxiliaries (to_int floor vars,
                // ITE selectors) that the search skips but the lowered
                // assertions still reference, leaving every candidate
                // indeterminate. The original form has only user variables
                // and CMS evaluates to_int/ite directly.
                CandidateModelSearch::Config cfg;
                cfg.assertionRootsOverride = originalAssertions_;
                cfg.allowUF = true;  // model UF apps + emit function tables
                CandidateModelSearch cms(*ir, logic, cfg);
                auto repaired = cms.run();
                if (repaired.found) {
                    auto saved = std::move(lastModel_);
                    lastModel_ = repaired.model;
                    if (modelViolatesOriginal()) lastModel_ = std::move(saved);
                }
            }
        } else if (result == SatSolver::SolveResult::Unsat) {
            ret = Result::Unsat;
        } else {
            // Cap. 10 — Validated CandidateModelSearch (SAT-only last
            // resort). The legacy complete engines returned Unknown for
            // this query (or hit a recovered SIGSEGV). Try a small set of
            // deterministic candidate assignments and accept the first
            // one that the arithmetic evaluator confirms satisfies every
            // original assertion. This NEVER returns UNSAT/Conflict/Lemma
            // — at worst it reports `found=false` and we keep Unknown.
            CandidateModelSearch cms(*ir, logic);
            auto cmsResult = cms.run();
            if (cmsResult.found) {
                lastModel_ = cmsResult.model;
                ret = Result::Sat;
            } else {
                if (lastUnknownReason_.empty()) {
                    lastUnknownReason_ = "SAT: solve returned Unknown (propagator abort or timeout)";
                }
                ret = Result::Unknown;
            }
        }

        // Partial-function (div/mod-by-zero) extension + soundness gate, applied
        // to EVERY Sat path (main propagator, model-repair, and CMS fallback).
        // Only relevant when a model is requested (Model-Validation track):
        // verdict soundness is unaffected. If the chosen extension is internally
        // inconsistent, or a Real `/` is applied at a 0 denominator (not emitted
        // in round 1), the printed model would be incomplete/unsound — downgrade
        // Sat -> Unknown rather than emit it.
        if (ret == Result::Sat && modelRequestedImpl()) {
            buildPartialFuncModel();
            if (partialFuncModel_.inconsistent || partialFuncModel_.realDivByZero) {
                lastUnknownReason_ =
                    partialFuncModel_.inconsistent
                        ? "partial-function model: inconsistent total extension"
                        : "partial-function model: Real division by zero (unsupported in model output)";
                lastModel_.reset();
                partialFuncModel_ = PartialFuncModel{};
                ret = Result::Unknown;
            }
        }

        // QF_AX array soundness gate (Model-Validation track only): when a
        // model is requested for an array problem, re-validate the extracted
        // array model against the ORIGINAL assertions. If it DEFINITELY
        // violates one, or we cannot build it, downgrade Sat -> Unknown rather
        // than emit an unvalidated array sat. The UNSAT verdict (sound axioms)
        // is never affected. Verdict soundness for SAT is independent of this
        // (the QF_AX theory check is complete); this only protects the printed
        // model and never returns sat without a validated model.
        if (ret == Result::Sat && modelRequestedImpl() && features.hasArray) {
            bool ok = arrayModelValidates();
            if (!ok) {
                lastUnknownReason_ =
                    "QF_AX: array model construction/validation incomplete (gated to Unknown)";
                lastModel_.reset();
                ret = Result::Unknown;
            }
        }

        // Array SAT soundness safety net (ALWAYS, incl. Single-Query track).
        // Even without :produce-models, build the array model internally and
        // validate. Only a DEFINITE violation downgrades Sat -> Unknown — this
        // catches a spurious array sat from a missed Row2/Ext instance that
        // would otherwise escape unvalidated. Indeterminate / no-model stays sat
        // (conservative: never spuriously reject a genuine sat). The build
        // happens here independently of modelRequestedImpl() so the same
        // validator runs on every array sat verdict.
        if (ret == Result::Sat && features.hasArray) {
            if (!lastModel_) lastModel_ = theoryManager.getModel();
            if (arrayModelDefinitelyViolates()) {
                lastUnknownReason_ =
                    "array: SAT model violates an original assertion "
                    "(missed array axiom instance) — gated to Unknown (sound)";
                lastModel_.reset();
                ret = Result::Unknown;
            }
        }

#ifdef ZOLVER_ENABLE_CASESTATS
        finalizeCaseStats(ret, solveDurMs, &propagator, &theoryManager,
                          cadicalBackend, &atomizer, &registry);
#endif
        return ret;
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

    const auto& expr = pImpl->ir->get(t.id());
    auto sortKind = pImpl->ir->sortKind(expr.sort);

    // Prefer the typed numeric channel (RealValue) when available: it carries
    // exact values including algebraic ones (e.g. √2 for x²=2), which the
    // legacy string channel cannot represent losslessly.
    if (pImpl->lastModel_ && std::holds_alternative<std::string>(expr.payload.value)) {
        const std::string& name = std::get<std::string>(expr.payload.value);
        const auto& num = pImpl->lastModel_->numericAssignments;
        auto nit = num.find(name);
        if (nit != num.end()) {
            const RealValue& rv = nit->second;
            if (sortKind == SortKind::Int && rv.isExactInteger()) {
                mpz_class fl = rv.floor();
                if (fl.fits_slong_p()) return mkInt(static_cast<int64_t>(fl.get_si()));
            }
            return mkReal(rv.toSmtLib2());
        }
    }

    // Legacy string channel.
    Model m = getModel();
    const std::string* val = m.getValue(t.id());
    if (!val) return Term{};

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

bool Solver::modelRequested() const {
    if (!pImpl || !pImpl->parser) return false;
    auto opts = pImpl->parser->getOptions();
    return opts && opts->get_model;
}

bool Solver::modelMatchesOriginal() const {
    if (!pImpl || !pImpl->ir || !pImpl->lastModel_) return true;  // nothing to disprove
    ArithModelValidator::NumAssignment numAsg;
    ArithModelValidator::BoolAssignment boolAsg;
    for (const auto& [name, val] : pImpl->lastModel_->assignments) {
        if (val == "true")  { boolAsg[name] = true;  continue; }
        if (val == "false") { boolAsg[name] = false; continue; }
        try { numAsg[name] = mpq_class(val); }
        catch (...) { /* unparseable → leave unassigned (indeterminate) */ }
    }
    ArithModelValidator validator(*pImpl->ir, numAsg, boolAsg);
    // Only a DEFINITE violation counts as "does not match".
    return validator.validate(pImpl->originalAssertions_)
           != ArithModelValidator::Verdict::Violated;
}

namespace {
// Format a model value string (as stored by the theory model — e.g. "5",
// "-3", "3/2", "true") into an SMT-LIB term of the given sort.
std::string formatModelValue(SortKind kind, const std::string& raw) {
    if (kind == SortKind::Bool) {
        return (raw == "true" || raw == "1") ? "true" : "false";
    }
    // Numeric: split optional sign and optional p/q.
    std::string s = raw;
    bool neg = false;
    if (!s.empty() && s[0] == '-') { neg = true; s = s.substr(1); }
    auto slash = s.find('/');
    std::string body;
    if (slash != std::string::npos) {
        std::string num = s.substr(0, slash);
        std::string den = s.substr(slash + 1);
        if (kind == SortKind::Int) {
            // An Int model value should be integral; if a denominator slipped
            // through, fall back to the numerator (defensive — shouldn't happen).
            body = (den == "1") ? num : num;
        } else {
            body = (den == "1") ? (num + ".0") : ("(/ " + num + " " + den + ")");
        }
    } else {
        body = (kind == SortKind::Real) ? (s + ".0") : s;
    }
    return neg ? ("(- " + body + ")") : body;
}
} // namespace

void Solver::dumpModel(std::ostream& os) const {
    // SMT-LIB 2.6 get-model response: a bare list of define-fun bindings,
    // one per user-declared 0-arity symbol. Values come from the last
    // theory model; unconstrained symbols get a sort-appropriate default.
    if (!pImpl) { os << "(\n)\n"; return; }

    const TheorySolver::TheoryModel* tm =
        pImpl->lastModel_ ? &*pImpl->lastModel_ : nullptr;

    // -----------------------------------------------------------------------
    // Array model token resolution (QF_AX + combination array logics).
    //
    // EufSolver::getModel() emits each array as an ArrayInterp over opaque
    // equality TOKENS for index/element values:
    //   "#n:<rational>" — a concrete number (combination logics: the bridged
    //                     select/index value flowing from the arith model);
    //   "#b:1"/"#b:0"   — a concrete bool;
    //   "@e..."/"@def..." — an opaque uninterpreted-sort element (QF_AX) or an
    //                     unconstrained index/element with no numeric pin.
    // The egraph compares these by EQUALITY ONLY, so the printed model must
    // assign each DISTINCT token a DISTINCT concrete value (preserving
    // disequalities) and each occurrence of the SAME token the SAME value
    // (preserving the asserted reads). We mint concrete values here:
    //   - numeric/bool tokens print as themselves;
    //   - opaque tokens in an Int/Real sort get a fresh integer (chosen to
    //     avoid colliding with any explicit numeric token in that array);
    //   - opaque tokens in an uninterpreted sort get an abstract constant
    //     "@<sort>!<n>" declared as a 0-arity symbol of that sort (z3-style,
    //     replayable). One namespace per uninterpreted sort.
    // This block computes tokenSmt(token, smtSort) -> printable SMT term and
    // collects the abstract-constant declarations to emit first.
    // -----------------------------------------------------------------------
    struct ArrayModelEmitter {
        // smtSort string -> kind classification.
        enum class SK { Int, Real, Bool, Uninterp };
        // Per-uninterpreted-sort: token -> abstract constant name.
        std::map<std::string, std::map<std::string, std::string>> uninterpConsts;
        // Per-uninterpreted-sort emission counter.
        std::map<std::string, int> uninterpCounter;
        // Int/Real opaque token -> chosen integer (global; Int values are
        // globally distinct so one namespace is fine), avoiding used numbers.
        std::map<std::string, std::string> numericOpaque;
        std::set<long long> usedNums;        // explicit numbers seen anywhere
        long long nextFreeNum = 0;

        static SK classify(const std::string& smtSort) {
            if (smtSort == "Int")  return SK::Int;
            if (smtSort == "Real") return SK::Real;
            if (smtSort == "Bool") return SK::Bool;
            return SK::Uninterp;
        }

        // Pre-scan: record every explicit numeric token so minted integers
        // never collide with a real value the formula constrained.
        void noteToken(const std::string& tok) {
            if (tok.rfind("#n:", 0) == 0) {
                try {
                    mpq_class q(tok.substr(3));
                    if (q.get_den() == 1 && q.get_num().fits_slong_p())
                        usedNums.insert(q.get_num().get_si());
                } catch (...) {}
            }
        }

        std::string freshNum() {
            while (usedNums.count(nextFreeNum)) ++nextFreeNum;
            long long v = nextFreeNum++;
            usedNums.insert(v);
            return std::to_string(v);
        }

        // Resolve a token to a printable SMT term of the given sort.
        std::string resolve(const std::string& tok, const std::string& smtSort) {
            SK k = classify(smtSort);
            if (tok.rfind("#b:", 0) == 0) return tok.substr(3) == "1" ? "true" : "false";
            if (tok.rfind("#n:", 0) == 0) {
                std::string body = tok.substr(3);
                return formatModelValue(k == SK::Real ? SortKind::Real : SortKind::Int, body);
            }
            // Opaque token.
            if (k == SK::Bool) return "false";  // unconstrained bool
            if (k == SK::Int || k == SK::Real) {
                auto it = numericOpaque.find(tok);
                std::string n;
                if (it != numericOpaque.end()) n = it->second;
                else { n = freshNum(); numericOpaque[tok] = n; }
                return formatModelValue(k == SK::Real ? SortKind::Real : SortKind::Int, n);
            }
            // Uninterpreted sort: abstract constant per token.
            auto& byTok = uninterpConsts[smtSort];
            auto it = byTok.find(tok);
            if (it != byTok.end()) return it->second;
            int idx = uninterpCounter[smtSort]++;
            std::string cname = "@" + smtSort + "!" + std::to_string(idx);
            byTok[tok] = cname;
            return cname;
        }
    } emit;

    // Build name -> declared array Sort (index/element SMT sort strings) for
    // every declared array variable, and pre-scan tokens for numeric collisions.
    struct ArrSorts { std::string idxSmt, elemSmt; };
    std::map<std::string, ArrSorts> arrSorts;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var || !var->isArray()) continue;
            auto s = var->getSort();
            if (!s) continue;
            auto is = s->getIndexSort(), es = s->getElemSort();
            if (!is || !es) continue;
            arrSorts[var->getName()] = {is->toString(), es->toString()};
        }
    }
    if (tm) {
        for (const auto& [aname, ai] : tm->arrayInterps) {
            emit.noteToken(ai.defaultVal);
            for (const auto& [ix, vl] : ai.entries) { emit.noteToken(ix); emit.noteToken(vl); }
        }
    }

    // Map each scalar (index/element) variable name to the SMT sort of any
    // array position it tokenizes into, so its opaque token resolves in the
    // SAME namespace the array entries use. We learn the sort from the parser
    // declaration of the scalar itself.
    auto scalarSmtSort = [&](const std::shared_ptr<SOMTParser::DAGNode>& v) -> std::string {
        if (v->isVBool()) return "Bool";
        if (v->isVInt())  return "Int";
        if (v->isVReal()) return "Real";
        auto s = v->getSort();
        return s ? s->toString() : "";
    };

    os << "(\n";

    // First emit array define-funs (so the scalar index/element values they
    // reference are resolved into emit's token maps before we print scalars,
    // keeping the two consistent). EVERY declared array variable must get a
    // define-fun (get-model completeness), even those absent from the theory
    // model (e.g. an array eliminated by read-over-write simplification, which
    // is then unconstrained → any const array is a valid witness).
    std::ostringstream arrayBuf;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var || !var->isArray()) continue;
            std::string name = var->getName();
            auto sortsIt = arrSorts.find(name);
            std::string idxSmt = sortsIt != arrSorts.end() ? sortsIt->second.idxSmt : "Int";
            std::string elemSmt = sortsIt != arrSorts.end() ? sortsIt->second.elemSmt : "Int";
            std::string arrSmt = "(Array " + idxSmt + " " + elemSmt + ")";

            std::string body;
            auto itAi = tm ? tm->arrayInterps.find(name)
                           : std::unordered_map<std::string,
                                 TheorySolver::TheoryModel::ArrayInterp>::const_iterator{};
            if (tm && itAi != tm->arrayInterps.end()) {
                const auto& ai = itAi->second;
                body = "((as const " + arrSmt + ") " +
                       emit.resolve(ai.defaultVal, elemSmt) + ")";
                std::string defv = emit.resolve(ai.defaultVal, elemSmt);
                for (const auto& [ix, vl] : ai.entries) {
                    // Skip entries that equal the default (no-op store).
                    std::string ixv = emit.resolve(ix, idxSmt);
                    std::string vlv = emit.resolve(vl, elemSmt);
                    if (vlv == defv) continue;
                    body = "(store " + body + " " + ixv + " " + vlv + ")";
                }
            } else {
                // Unconstrained array: a const array over a fresh element value.
                body = "((as const " + arrSmt + ") " +
                       emit.resolve("@unconstrained_arr_default:" + name, elemSmt) + ")";
            }
            arrayBuf << "  (define-fun " << name << " () " << arrSmt << " "
                     << body << ")\n";
        }
    }

    // Scalar variables (Int/Real/Bool AND uninterpreted index/element vars).
    std::ostringstream scalarBuf;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var) continue;
            if (var->isArray()) continue;  // handled above
            std::string name = var->getName();
            std::string smtSort = scalarSmtSort(var);
            if (smtSort.empty()) continue;
            ArrayModelEmitter::SK kind = ArrayModelEmitter::classify(smtSort);

            // Algebraic values (irrational roots) live in the typed RealValue
            // channel; emit their exact root-of form directly.
            if (tm && kind == ArrayModelEmitter::SK::Real) {
                auto rvIt = tm->numericAssignments.find(name);
                if (rvIt != tm->numericAssignments.end() && rvIt->second.isAlgebraic()) {
                    scalarBuf << "  (define-fun " << name << " () Real "
                              << rvIt->second.toSmtLib2() << ")\n";
                    continue;
                }
            }

            std::string raw;
            if (tm) {
                auto it = tm->assignments.find(name);
                if (it != tm->assignments.end()) raw = it->second;
            }
            std::string valTerm;
            if (raw.empty()) {
                // Unconstrained.
                if (kind == ArrayModelEmitter::SK::Bool) valTerm = "false";
                else if (kind == ArrayModelEmitter::SK::Uninterp)
                    valTerm = emit.resolve("@unconstrained:" + name, smtSort);
                else valTerm = formatModelValue(
                    kind == ArrayModelEmitter::SK::Real ? SortKind::Real : SortKind::Int, "0");
            } else if (raw == "true" || raw == "false") {
                valTerm = raw;
            } else {
                // May be a plain number (arith model) or a token (EUF model).
                if (raw.rfind("#n:", 0) == 0 || raw.rfind("#b:", 0) == 0 ||
                    raw.rfind("@", 0) == 0) {
                    valTerm = emit.resolve(raw, smtSort);
                } else if (kind == ArrayModelEmitter::SK::Uninterp) {
                    valTerm = emit.resolve(raw, smtSort);
                } else {
                    valTerm = formatModelValue(
                        kind == ArrayModelEmitter::SK::Real ? SortKind::Real :
                        kind == ArrayModelEmitter::SK::Int  ? SortKind::Int  :
                        SortKind::Bool, raw);
                }
            }
            scalarBuf << "  (define-fun " << name << " () " << smtSort << " "
                      << valTerm << ")\n";
        }
    }

    // Emit abstract-constant declarations for uninterpreted-sort elements
    // FIRST (they are referenced by the array/scalar define-funs that follow).
    for (const auto& [sortName, byTok] : emit.uninterpConsts) {
        for (const auto& [tok, cname] : byTok) {
            os << "  (declare-fun " << cname << " () " << sortName << ")\n";
        }
    }
    os << arrayBuf.str();
    os << scalarBuf.str();

    // Uninterpreted function interpretations: a finite table emitted as a
    // nested ite over the asserted argument tuples, with a default for any
    // other input. Populated by the validated candidate search (QF_UF*).
    if (tm && !tm->functionInterps.empty()) {
        auto kindOf = [](const std::string& s) -> SortKind {
            if (s == "Int")  return SortKind::Int;
            if (s == "Bool") return SortKind::Bool;
            return SortKind::Real;
        };
        for (const auto& [fname, fi] : tm->functionInterps) {
            // Internal div/mod-by-zero carriers are re-expressed as `div`/`mod`
            // define-fun shadows below; never emit the __undef_* symbols, which
            // the model validator does not recognize.
            if (fname.rfind("__undef", 0) == 0) continue;
            os << "  (define-fun " << fname << " (";
            for (size_t i = 0; i < fi.argSorts.size(); ++i) {
                if (i) os << " ";
                os << "(x!" << i << " " << fi.argSorts[i] << ")";
            }
            SortKind retKind = kindOf(fi.retSort);
            os << ") " << fi.retSort << " ";
            std::string body =
                formatModelValue(retKind, fi.deflt.empty() ? "0" : fi.deflt);
            for (auto it = fi.entries.rbegin(); it != fi.entries.rend(); ++it) {
                std::string cond;
                if (it->args.size() == 1) {
                    cond = "(= x!0 " +
                           formatModelValue(kindOf(fi.argSorts[0]), it->args[0]) + ")";
                } else {
                    cond = "(and";
                    for (size_t i = 0; i < it->args.size(); ++i) {
                        cond += " (= x!" + std::to_string(i) + " " +
                                formatModelValue(kindOf(fi.argSorts[i]), it->args[i]) + ")";
                    }
                    cond += ")";
                }
                body = "(ite " + cond + " " +
                       formatModelValue(retKind, it->value) + " " + body + ")";
            }
            os << body << ")\n";
        }
    }

    // Partial theory functions (div/mod by zero): emit define-fun shadows that
    // give our chosen value at the undefined (divisor-0) inputs and otherwise
    // call the original theory function. The body may call the same-named
    // theory function — this is shadowing, not recursion (SMT-COMP 2026 model
    // format). The zero-branch is a nested-ite over the dividend a; any unlisted
    // zero-divisor input falls through to 0 (free choice for unconstrained
    // inputs).
    {
        const auto& pfm = pImpl->partialFuncModel_;
        auto zeroBranch = [](const std::map<mpq_class, mpq_class>& tbl) -> std::string {
            std::string body = "0";
            for (auto it = tbl.rbegin(); it != tbl.rend(); ++it) {
                body = "(ite (= a " + formatModelValue(SortKind::Int, it->first.get_str()) +
                       ") " + formatModelValue(SortKind::Int, it->second.get_str()) +
                       " " + body + ")";
            }
            return body;
        };
        if (!pfm.divZero.empty()) {
            os << "  (define-fun div ((a Int) (b Int)) Int (ite (= b 0) "
               << zeroBranch(pfm.divZero) << " (div a b)))\n";
        }
        if (!pfm.modZero.empty()) {
            os << "  (define-fun mod ((a Int) (b Int)) Int (ite (= b 0) "
               << zeroBranch(pfm.modZero) << " (mod a b)))\n";
        }
    }
    os << ")\n";
}
Proof Solver::getProof() const { return Proof{}; }
Statistics Solver::getStatistics() const { return Statistics{}; }

std::string Solver::lastUnknownReason() const { return pImpl->lastUnknownReason_; }
std::string Solver::lastUnknownCode() const { return pImpl->lastUnknownCode_; }
std::string Solver::lastUnknownComponent() const { return pImpl->lastUnknownComponent_; }
std::string Solver::lastUnknownDetail() const { return pImpl->lastUnknownDetail_; }

#ifdef ZOLVER_ENABLE_CASESTATS
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

} // namespace zolver
