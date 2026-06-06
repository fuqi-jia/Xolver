#include "xolver/Solver.h"
#include "xolver/Result.h"
#include "expr/ir.h"
#include "theory/euf/EufSolver.h"
#include "expr/CoreIteLowerer.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/BoolSubtermPurifier.h"
#include "frontend/preprocess/UfInArithPurifier.h"
#include "frontend/preprocess/RealDivLowerer.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include "frontend/preprocess/IntDivModConstantFold.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "theory/arith/nia/reasoners/ModEqConstFact.h"
#include "theory/arith/nia/NiaSolver.h"  // Track A Phase 1.3: solverFor handoff
#include "frontend/preprocess/ZoharBwiAxiomEmitter.h"
#include "frontend/preprocess/ModularConsistencyChecker.h"
#include "frontend/preprocess/NaryDistinctLowerer.h"
#include "frontend/preprocess/ToRealLiteralFold.h"
#include "frontend/preprocess/UnconditionalConstantPropagation.h"
#include "frontend/preprocess/FormulaRewriter.h"
#include "frontend/preprocess/MonomialSharingPass.h"
#include "frontend/preprocess/SolveEqs.h"
#include "frontend/preprocess/ModelConverter.h"
#include "frontend/preprocess/UnconstrainedElim.h"
#include "frontend/factory/StrategyPresets.h"
#include <cstdlib>
#include "theory/arith/search/CandidateModelSearch.h"
#include "proof/ArithModelValidator.h"
#include <gmpxx.h>
#include "expr/Smt2Dumper.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "frontend/atomization/Atomizer.h"
#include "theory/arith/nia/farkas/FarkasOrDetector.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "frontend/factory/TheoryFactory.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/bit_blast/EagerBitBlastSolver.h"
#ifdef XOLVER_ENABLE_CASESTATS
#ifdef XOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif
#endif
#include "util/EnvParam.h"
#include "util/SolveClock.h"

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
#include <thread>
#include <atomic>

namespace xolver {

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
    // Path of the file this problem was parsed from, retained so the portfolio
    // executor (XOLVER_STRAT_PORTFOLIO) can re-establish PRISTINE state per arm
    // via reset()+parseFile. Cleared by a programmatic assertFormula (which
    // would be lost on re-parse), which forces the executor to single-arm.
    std::string sourcePath_;
    // The CaDiCaL backend of the in-flight checkSatInternal, published so the
    // portfolio's per-arm budget watchdog can async-interrupt a running solve
    // (CaDiCaL terminate() is thread-safe). nullptr whenever no solve is live;
    // an RAII guard in checkSatInternal clears it on every exit path.
    std::atomic<CadicalBackend*> activeBackend_{nullptr};

    // Records variables eliminated by solve-eqs (XOLVER_PP_SOLVE_EQS) so their
    // values can be replayed onto the final model (↔SAT replay correctness).
    // Reset at the start of each checkSat's preprocessing; empty when the pass
    // did not run (flag off / incremental scope).
    ModelConverter modelConverter_;

    // Constants bound by UnconditionalConstantPropagation (Cap 8a). Captured
    // immediately after `cprop.commit()` so model emission and validators can
    // fill in user vars that UCP substituted away (the post-UCP IR has only
    // the source-of-binding equality at top-level; nested ones get folded to
    // `true`, leaving the var absent from downstream theories and therefore
    // absent from the printed model — defaults to 0, validator flags
    // false-SAT). Sound: every model of the original formula satisfies these
    // bindings by construction of UCP.
    std::unordered_map<std::string, mpq_class> fixedBindings_;

    // Partial-function (div/mod-by-zero) model support. divModOrigins_ is
    // captured from IntDivModLowerer; partialFuncModel_ is the chosen total
    // extension at undefined inputs, built from the final model (see
    // buildPartialFuncModel) and emitted as define-fun shadows in dumpModel.
    std::vector<DivModOrigin> divModOrigins_;
    // Track A Phase 1.3 — facts captured from IntDivModLowerer for the
    // native ModEqConstReasoner. Handed off to NiaSolver after setupSolvers.
    ModEqConstFactList modEqConstFacts_;
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

    // Merge UCP fixedBindings_ into lastModel_'s string + numeric channels for
    // any var not already present. Called at every site that sets lastModel_
    // so validators (modelViolatesOriginal, combinationModelDefinitelyViolates,
    // arrayModelValidates) and emit (Solver::getModel, dumpModel) all see the
    // eliminated user vars at their UCP-bound constants instead of defaulting
    // to 0 and flagging a false-SAT.
    void mergeFixedBindings() {
        if (!lastModel_ || fixedBindings_.empty()) return;
        for (const auto& [name, value] : fixedBindings_) {
            if (lastModel_->assignments.find(name) == lastModel_->assignments.end()) {
                lastModel_->assignments[name] = value.get_str();
            }
            if (lastModel_->numericAssignments.find(name) ==
                lastModel_->numericAssignments.end()) {
                lastModel_->numericAssignments.emplace(
                    name, RealValue::fromMpq(value));
            }
        }
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
        // XOLVER_DIAG_AM (diagnostic only): dump the array model + per-assertion
        // verdict so a floored array sat can be root-caused (which assertion,
        // which interp). Never affects the verdict.
        if (std::getenv("XOLVER_DIAG_AM")) {
            std::cerr << "[DIAG_AM] arrayInterps (" << lastModel_->arrayInterps.size() << "):\n";
            for (const auto& [nm, ai] : lastModel_->arrayInterps) {
                std::cerr << "  " << nm << " deflt=" << ai.defaultVal
                          << " entries=" << ai.entries.size() << ": ";
                for (const auto& [i, v] : ai.entries) std::cerr << "[" << i << "->" << v << "]";
                std::cerr << "\n";
            }
            std::cerr << "[DIAG_AM] scalar tokens: ";
            for (const auto& [nm, val] : lastModel_->assignments) std::cerr << nm << "=" << val << " ";
            std::cerr << "\n";
            for (size_t ai = 0; ai < originalAssertions_.size(); ++ai) {
                auto vd = validator.validate({originalAssertions_[ai]});
                if (vd == ArithModelValidator::Verdict::Violated)
                    std::cerr << "[DIAG_AM] VIOLATED assertion #" << ai << "\n";
            }
        }
        return validator.validate(originalAssertions_)
               == ArithModelValidator::Verdict::Violated;
    }

    // UF-combination soundness floor (QF_UFLIA / QF_UFLRA proper, no array).
    // Mirrors arrayModelDefinitelyViolates but routes function interpretations
    // from the EUF Track-3 model so UF apps over arith args evaluate concretely
    // instead of returning Indeterminate. Returns true ONLY on a DEFINITE
    // Violated — Indeterminate / unknown stays sat (never spuriously reject a
    // genuine sat). Catches the Wisa-class false-SAT: arith picks fmt1 such
    // that select_format(fmt1) value matches percent locally, but EUF never
    // had to merge them, so the negated goal is "satisfied" only because the
    // joint model is inconsistent — the validator's funcInterp table resolves
    // it concretely and exposes the violation.
    bool combinationModelDefinitelyViolates() const {
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
        if (!lastModel_->functionInterps.empty()) {
            validator.setFunctionInterps(&lastModel_->functionInterps);
        }
        return validator.validate(originalAssertions_)
               == ArithModelValidator::Verdict::Violated;
    }

    // STRICT model validation (XOLVER_PP_STRICT_VALIDATION). Returns true ONLY
    // when the extracted model POSITIVELY satisfies every original assertion
    // (Verdict::Satisfied). Unlike the *Violates helpers (which act only on a
    // DEFINITE violation), this is the trust gate: an unconfirmed model
    // (Indeterminate — missing assignment, uninterpreted function, construct the
    // validator cannot evaluate) is NOT accepted as sat. We populate declared
    // user variables with the same 0/false defaults dumpModel emits, so the
    // model checked here is exactly the one that would be printed.
    bool modelPositivelyValidates() const {
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
        // Opaque-EUF-token scalars: a combination scalar whose model value is an
        // EUF equality-class token ("@e6") has its AUTHORITATIVE identity in the
        // token channel (distinct token = distinct class). The typed numeric
        // channel, however, can carry a SPURIOUS value for it — the unconstrained-
        // scalar backfill mints 0, so two asserted-distinct scalars (i != j) both
        // become 0 and `(not (= i j))` spuriously evaluates FALSE -> the genuine
        // sat is over-floored to unknown (the alia_005/alra_010 class; verified by
        // instrumenting ArithModelValidator: token pass = both assertions TRUE,
        // real pass = i=j=0 -> assertion FALSE). Route these scalars through the
        // token channel ONLY: drop them from numAsg, the 0-defaulting, AND the
        // real channel. Sound (only ever sat->unknown; an unsat formula like read2
        // is still violated under the EUF arrangement) and SCOPED to "@" tokens —
        // NIA/LIA real models carry concrete rationals (never "@"), so the
        // default-on niaSatFloor is untouched.
        std::unordered_set<std::string> opaqueScalar;
        for (const auto& [name, val] : lastModel_->assignments)
            if (!val.empty() && val[0] == '@') opaqueScalar.insert(name);
        // Prefer the typed numeric channel (RealValue): exact rationals + the
        // combination shared-scalar's true arithmetic value. Skip opaque-token
        // scalars (their numeric value is the spurious collapse).
        std::unordered_map<std::string, RealValue> filteredReal;
        for (const auto& [name, rv] : lastModel_->numericAssignments) {
            if (opaqueScalar.count(name)) continue;
            filteredReal.emplace(name, rv);
            if (auto q = rv.tryAsRational()) numAsg[name] = *q;
        }
        // Mirror dumpModel's defaulting of unconstrained user variables so the
        // validated model matches the printed one (a var the theory left
        // unassigned is emitted as 0 / false) — EXCEPT opaque-token scalars,
        // which keep their EUF token identity instead of collapsing to 0.
        if (parser) {
            for (const auto& var : parser->getDeclaredVariables()) {
                if (!var) continue;
                std::string nm = var->getName();
                if (var->isVBool()) { if (!boolAsg.count(nm)) boolAsg[nm] = false; }
                else if (var->isVInt() || var->isVReal()) {
                    if (!numAsg.count(nm) && !opaqueScalar.count(nm)) numAsg[nm] = mpq_class(0);
                }
            }
        }
        const bool validatorMemo = std::getenv("XOLVER_PP_VALIDATOR_MEMO") != nullptr;
        ArithModelValidator::Verdict v;
        if (!lastModel_->arrayInterps.empty()) {
            ArithModelValidator validator(*ir, numAsg, boolAsg,
                                          lastModel_->arrayInterps, tokAsg);
            validator.setFunctionInterps(&lastModel_->functionInterps);
            validator.setRealAssignments(&filteredReal);
            validator.setEvalMemo(validatorMemo);
            v = validator.validate(originalAssertions_);
        } else {
            ArithModelValidator validator(*ir, numAsg, boolAsg);
            validator.setFunctionInterps(&lastModel_->functionInterps);
            validator.setRealAssignments(&filteredReal);
            validator.setEvalMemo(validatorMemo);
            v = validator.validate(originalAssertions_);
        }
        return v == ArithModelValidator::Verdict::Satisfied;
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

#ifdef XOLVER_ENABLE_CASESTATS
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
#ifdef XOLVER_ENABLE_CASESTATS
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
        sourcePath_.clear();
        divModOrigins_.clear();
        partialFuncModel_ = PartialFuncModel{};
        lastUnknownReason_.clear();
        lastUnknownCode_.clear();
        lastUnknownComponent_.clear();
        lastUnknownDetail_.clear();
#ifdef XOLVER_ENABLE_CASESTATS
        caseStats_ = CaseStats{};
#endif
    }

    bool parseFile(std::string_view filename) {
        parser = std::make_unique<SOMTParser::Parser>();
        // DIAG (XOLVER_NO_EXPAND_FUNCTIONS): toggle define-fun inlining to confirm
        // whether parse-time expansion is the Certora blowup. Not for production.
        parser->setOption("expand_functions",
                          std::getenv("XOLVER_NO_EXPAND_FUNCTIONS") == nullptr);
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
        sourcePath_ = std::string(filename);  // re-parseable source (portfolio)
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

    // Portfolio executor (XOLVER_STRAT_PORTFOLIO). Runs the ordered arms from
    // selectPortfolio until one returns a definitive (Sat/Unsat) verdict. Each
    // arm is run from PRISTINE state — the first arm uses the already-parsed
    // problem; subsequent arms reset()+re-parse the source file — so trying
    // several configurations is sound (any arm's Sat/Unsat is already
    // ModelValidator-backed; arms differ only in completeness). Multi-arm needs
    // a re-parseable file source; otherwise (programmatic input) it degrades to
    // a single arm. Phase 1 has one arm == XOLVER_STRAT_PRESETS, so a portfolio
    // run is behavior-neutral until the master populates differentiated arms.
    Result checkSatPortfolio() {
        const std::string path = sourcePath_;  // reset() clears it; capture first
        std::vector<PortfolioArm> arms = selectPortfolio(logic, LogicFeatures{});
        if (arms.empty()) return checkSatInternal();
        // Multi-arm requires a re-parseable file source.
        const bool canReparse = !path.empty();
        const size_t nArms = (canReparse ? arms.size() : 1);

        // Snapshot the user's env for every flag any arm touches, so that
        // between arms we can restore it and each arm sees (user env + its own
        // flags), with the user's explicit env always winning (overwrite=0).
        std::set<std::string> names;
        for (size_t i = 0; i < nArms; ++i) {
            if (arms[i].config.enableRewrite) names.insert("XOLVER_PP_REWRITE");
            for (const auto& f : arms[i].config.envFlags) names.insert(f.first);
        }
        std::map<std::string, std::optional<std::string>> baseline;
        for (const auto& n : names) {
            const char* v = std::getenv(n.c_str());
            baseline[n] = v ? std::optional<std::string>(v) : std::nullopt;
        }
        auto restoreEnv = [&]() {
            for (const auto& [n, v] : baseline) {
                if (v) setenv(n.c_str(), v->c_str(), 1);
                else   unsetenv(n.c_str());
            }
        };
        auto applyArm = [&](const PortfolioArm& a) {
            restoreEnv();  // back to the user's baseline, then layer this arm's
            // flags WITHOUT overriding an explicit user env (overwrite=0).
            if (a.config.enableRewrite) setenv("XOLVER_PP_REWRITE", "1", 0);
            for (const auto& [n, val] : a.config.envFlags)
                setenv(n.c_str(), val.c_str(), 0);
        };

        Result r = Result::Unknown;
        for (size_t i = 0; i < nArms; ++i) {
            // Apply the arm's env flags BEFORE (re-)parsing. Theory solvers read
            // their flags (e.g. XOLVER_LIA_CUTS / XOLVER_LIA_GMI_CUTS) once in
            // their constructor, which runs inside parseFile -> setupSolvers; if
            // applyArm ran after the reparse the reconstructed solvers would miss
            // the arm's flags and every differentiated arm would silently collapse
            // to the base config. Arm 0 reuses the already-parsed problem (parsed
            // under the user env); a base arm 0 carries no extra flags, so that is
            // exactly the user's configuration.
            applyArm(arms[i]);
            if (i > 0) {                       // pristine state for arm 2..N
                reset();
                if (!parseFile(path)) break;   // source vanished -> stop, keep best
            }
            r = runArmWithBudget(arms[i].budgetMs);
            if (r == Result::Sat || r == Result::Unsat) break;  // definitive wins
        }
        restoreEnv();  // leave the process env as the user had it
        return r;
    }

    // Run one already-applied arm, optionally under a wall-clock budget. With a
    // positive budget, a watchdog thread async-interrupts the SAT solve once the
    // deadline passes (-> Unknown), so the portfolio falls through to the next
    // arm. budget <= 0 runs the arm to completion thread-free (the default /
    // Phase-1 path, so the common case takes no thread). Interrupting only ever
    // turns a verdict into Unknown, so it can never change a sat/unsat answer.
    Result runArmWithBudget(int budgetMs) {
        if (budgetMs <= 0) return checkSatInternal();

        std::atomic<bool> done{false};
        std::thread watchdog([this, budgetMs, &done]() {
            const auto deadline = std::chrono::steady_clock::now() +
                                  std::chrono::milliseconds(budgetMs);
            while (!done.load(std::memory_order_acquire)) {
                if (std::chrono::steady_clock::now() >= deadline) {
                    if (CadicalBackend* b =
                            activeBackend_.load(std::memory_order_acquire)) {
                        b->requestTerminate();  // thread-safe async interrupt
                    }
                    return;
                }
                std::this_thread::sleep_for(std::chrono::milliseconds(2));
            }
        });
        Result r = checkSatInternal();
        done.store(true, std::memory_order_release);
        watchdog.join();
        return r;
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

        // Coarse phase timing (SOLVE_PHASE_PROF) to localize a pre-solve hang.
        // Flushed to stderr so a timeout-killed run shows the last phase entered.
        static const bool phaseProf = std::getenv("SOLVE_PHASE_PROF") != nullptr;
        auto phaseClock = std::chrono::steady_clock::now();
        auto phase = [&](const char* nm) {
            if (!phaseProf) return;
            auto now = std::chrono::steady_clock::now();
            std::cerr << "[PHASE] " << nm << "  +"
                      << std::chrono::duration_cast<std::chrono::milliseconds>(now - phaseClock).count()
                      << "ms (asserts=" << ir->assertions().size() << ")" << std::endl;
            phaseClock = now;
        };
        phase("enter");

        // XOLVER_PP_REWRITE (Agent 5): generic DAG-safe memoized fixpoint
        // formula rewriter. Runs BEFORE ITE lowering so its simplifications
        // (boolean identities/absorption, const-fold, relational const-eval)
        // shrink the formula for every downstream pass. Sound: it only APPENDS
        // CoreExpr nodes, so the originalAssertions_ snapshot above keeps
        // referencing the original formula for ModelValidator. A top-level
        // assertion that simplifies to the boolean constant false makes the
        // assertion conjunction unsatisfiable.
        if (std::getenv("XOLVER_PP_AND_FLATTEN") && ir->currentScopeLevel() == 0) {
            std::vector<std::pair<ScopeLevel, ExprId>> flat;
            std::function<void(ScopeLevel, ExprId)> push = [&](ScopeLevel lvl, ExprId e) {
                const CoreExpr& n = ir->get(e);
                if (n.kind == Kind::And) {
                    for (ExprId c : n.children) push(lvl, c);
                } else {
                    flat.push_back({lvl, e});
                }
            };
            bool anyAnd = false;
            size_t origSize = 0;
            {
                const auto& scoped = ir->getScopedAssertions();
                origSize = scoped.size();
                for (const auto& [lvl, e] : scoped) {
                    if (ir->get(e).kind == Kind::And) anyAnd = true;
                    push(lvl, e);
                }
            }
            if (anyAnd && flat.size() > origSize) {
                ir->clearAssertions();
                for (const auto& [lvl, e] : flat) ir->addAssertion(e, lvl);
                std::cerr << "[AndFlatten] " << origSize
                          << " -> " << flat.size() << " assertions\n";
            }
        }

        // ---------------- Bounded-global Cartesian enumeration -----------
        // XOLVER_PP_BOUNDED_ENUM (default-OFF): when an Int variable has
        // top-level bounds `(>= v c1) ∧ (<= v c2)` with small domain
        // (c2 - c1 + 1 ≤ kMaxBoundedDomain), replace the bounds with a
        // disjunction `(or (= v c1) (= v c1+1) ... (= v c2))`. This lets
        // SAT case-split on v's concrete value; the bilinear products
        // `(* v lambda)` then collapse to linear `c * lambda` per branch,
        // routing the residual to the LIA reasoner.
        //
        // Targets the SAT14 cluster (588/775/1882): pure-conjunction
        // Farkas systems with 2-3 bounded globals (typically [-1,1]),
        // total 3^N ≤ 27 cases.
        //
        // Sound: `(>= v c1) ∧ (<= v c2)` over Z is logically equivalent
        // to `(or (= v c1) ... (= v c2))`.
        if (std::getenv("XOLVER_PP_BOUNDED_ENUM") && ir->currentScopeLevel() == 0) {
            SortId intSort = ir->intSortId();
            std::unordered_map<std::string, std::pair<mpz_class, mpz_class>> bnd;
            std::unordered_map<std::string, std::pair<size_t, size_t>> idx;
            const auto& scoped = ir->getScopedAssertions();
            // Pre-pass: find `(>= v c)` and `(<= v c)` over Int vars.
            std::function<bool(const CoreExpr&, mpz_class&)> tryConst =
                [&](const CoreExpr& n, mpz_class& out) -> bool {
                if (n.kind == Kind::ConstInt || n.kind == Kind::ConstReal) {
                    if (auto* iv = std::get_if<int64_t>(&n.payload.value)) { out = mpz_class(*iv); return true; }
                    if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
                        try { mpq_class q(*sv); if (q.get_den() != 1) return false; out = q.get_num(); return true; }
                        catch (...) { return false; }
                    }
                }
                if (n.kind == Kind::Neg && n.children.size() == 1) {
                    mpz_class inner;
                    if (tryConst(ir->get(n.children[0]), inner)) { out = -inner; return true; }
                }
                return false;
            };
            auto tryVar = [&](const CoreExpr& n, std::string& out) -> bool {
                if (n.kind != Kind::Variable) return false;
                if (auto* s = std::get_if<std::string>(&n.payload.value)) { out = *s; return true; }
                return false;
            };
            for (size_t i = 0; i < scoped.size(); ++i) {
                ExprId aid = scoped[i].second;
                const CoreExpr& a = ir->get(aid);
                if (a.kind != Kind::Geq && a.kind != Kind::Leq) continue;
                if (a.children.size() != 2) continue;
                const CoreExpr& lhs = ir->get(a.children[0]);
                const CoreExpr& rhs = ir->get(a.children[1]);
                // Try both orderings: (rel var const) or (rel const var).
                std::string vn;
                mpz_class c;
                Kind effectiveKind = a.kind;
                bool ok = false;
                if (tryVar(lhs, vn) && tryConst(rhs, c)) {
                    ok = true; // (rel var c) -- kind stays as parsed
                } else if (tryConst(lhs, c) && tryVar(rhs, vn)) {
                    // (Leq c v) == (Geq v c); (Geq c v) == (Leq v c).
                    effectiveKind = (a.kind == Kind::Leq) ? Kind::Geq : Kind::Leq;
                    ok = true;
                }
                if (!ok) continue;
                // Sort check on the var (lookup the var node).
                ExprId varEid = (lhs.kind == Kind::Variable) ? a.children[0] : a.children[1];
                if (ir->get(varEid).sort != intSort && intSort != NullSort) continue;
                auto& entry = bnd[vn];
                auto& ixe = idx[vn];
                if (effectiveKind == Kind::Geq) {
                    if (ixe.first == 0 || c > entry.first) { entry.first = c; ixe.first = i + 1; }
                } else {
                    if (ixe.second == 0 || c < entry.second) { entry.second = c; ixe.second = i + 1; }
                }
            }
            // Build replacement assertions for vars with finite integer
            // domains. NO per-variable cap (that would be a magic budget).
            // The only guard is the total Cartesian-product size below, to
            // prevent formula-size explosion on million-domain vars -- that
            // is a sound formula-size sanity check, not a verdict cap.
            std::vector<std::pair<std::string, std::pair<mpz_class, mpz_class>>> elig;
            mpz_class cartesian = 1;
            // Sort candidates by domain size ascending so we include small
            // domains first (most likely to be useful enumeration targets).
            std::vector<std::tuple<mpz_class, std::string, std::pair<mpz_class, mpz_class>>> ranked;
            for (const auto& [v, p] : bnd) {
                const auto& [lo, hi] = p;
                const auto& ixe = idx[v];
                if (ixe.first == 0 || ixe.second == 0) continue;
                mpz_class span = hi - lo + 1;
                if (span < 1) continue;
                ranked.push_back({span, v, p});
            }
            std::sort(ranked.begin(), ranked.end(),
                      [](const auto& a, const auto& b) {
                          return std::get<0>(a) < std::get<0>(b);
                      });
            // Cap total Cartesian product so we don't expand a single
            // huge-domain var into millions of Or branches. 256 is the
            // honest formula-size sanity check.
            constexpr long kMaxCartesian =
                256;  // formula-size sanity (NOT a verdict cap)
            long cartesianLim = static_cast<long>(env::paramLong(
                "XOLVER_PP_BOUNDED_ENUM_MAX_CARTESIAN", kMaxCartesian));
            for (auto& [span, v, p] : ranked) {
                if ((cartesian * span) > cartesianLim) break;
                cartesian *= span;
                elig.push_back({v, p});
            }
            if (!elig.empty()) {
                std::vector<std::pair<ScopeLevel, ExprId>> kept;
                std::unordered_set<size_t> dropIdx;
                for (const auto& e : elig) {
                    dropIdx.insert(idx[e.first].first - 1);
                    dropIdx.insert(idx[e.first].second - 1);
                }
                for (size_t i = 0; i < scoped.size(); ++i) {
                    if (dropIdx.count(i)) continue;
                    kept.push_back(scoped[i]);
                }
                for (const auto& [v, p] : elig) {
                    const auto& [lo, hi] = p;
                    CoreExpr varN;
                    varN.kind = Kind::Variable;
                    varN.sort = intSort;
                    varN.payload = Payload(v);
                    ExprId varEid = ir->addShared(std::move(varN));
                    SmallVector<ExprId, 4> orC;
                    for (mpz_class c = lo; c <= hi; ++c) {
                        if (!c.fits_slong_p()) { orC.clear(); break; }
                        CoreExpr ce;
                        ce.kind = Kind::ConstInt;
                        ce.sort = intSort;
                        ce.payload = Payload(static_cast<int64_t>(c.get_si()));
                        ExprId cEid = ir->addShared(std::move(ce));
                        CoreExpr eq;
                        eq.kind = Kind::Eq;
                        eq.sort = boolSortId_;
                        eq.children = SmallVector<ExprId,4>{varEid, cEid};
                        orC.push_back(ir->addShared(std::move(eq)));
                    }
                    if (orC.empty()) continue;
                    ExprId enumE;
                    if (orC.size() == 1) enumE = orC[0];
                    else {
                        CoreExpr orN;
                        orN.kind = Kind::Or;
                        orN.sort = boolSortId_;
                        for (ExprId c : orC) orN.children.push_back(c);
                        enumE = ir->addShared(std::move(orN));
                    }
                    kept.push_back({scoped[0].first, enumE});
                }
                ir->clearAssertions();
                for (const auto& [lv, eid] : kept) ir->addAssertion(eid, lv);
                std::cerr << "[BoundedEnum] " << elig.size()
                          << " var(s) enumerated; " << dropIdx.size()
                          << " bound atom(s) replaced\n";
            }
        }

        // ---------------- Newton-Raphson integer-sqrt prover --------------
        // XOLVER_PP_NEWTON_INT_SQRT (default-OFF): detect Newton iteration
        //   (= V (div (+ U (div X U)) 2))
        // and the standard hypotheses
        //   (<= (* U U) X)              # oldres² ≤ x
        //   (<= X (* C (* U U)))        # x ≤ C * oldres² for some C ≥ 1
        // When matched, emit TWO proven lemmas (see
        // docs/newton-integer-sqrt-analysis.md for full derivation):
        //   Lemma 1: (< X (* (+ V 1) (+ V 1)))         -- branch-1 contradiction
        //   Lemma 2: (<= (* V V) (div (* 15625 X) 10000)) -- 16*V² ≤ 25*X
        // Together these close sqrtStep1/1a UNSAT proofs.
        //
        // Sound: both lemmas algebraically follow from the hypotheses by
        // completed-square arithmetic.
        if (std::getenv("XOLVER_PP_NEWTON_INT_SQRT") && ir->currentScopeLevel() == 0) {
            SortId intSort = ir->intSortId();
            const auto& scoped = ir->getScopedAssertions();
            auto isVar = [&](const CoreExpr& n) -> bool {
                return n.kind == Kind::Variable;
            };
            auto isConstInt = [&](const CoreExpr& n, int64_t v) -> bool {
                if (n.kind != Kind::ConstInt && n.kind != Kind::ConstReal) return false;
                if (auto* iv = std::get_if<int64_t>(&n.payload.value)) return *iv == v;
                if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
                    try { mpq_class q(*sv); return q.get_den() == 1 && q.get_num() == v; }
                    catch (...) { return false; }
                }
                return false;
            };
            auto eqExpr = [&](ExprId a, ExprId b) -> bool { return a == b; };
            // Step 1: collect candidate Newton triples (V, U, X) from
            // `(= V (div (+ U (div X U)) 2))` shapes.
            struct Match { ExprId V, U, X; };
            std::vector<Match> matches;
            for (const auto& [lvl, aid] : scoped) {
                const CoreExpr& a = ir->get(aid);
                if (a.kind != Kind::Eq || a.children.size() != 2) continue;
                // Try both child orderings for V.
                for (int swap = 0; swap < 2; ++swap) {
                    ExprId vEid = a.children[swap ? 1 : 0];
                    ExprId rhsEid = a.children[swap ? 0 : 1];
                    const CoreExpr& vN = ir->get(vEid);
                    if (!isVar(vN)) continue;
                    const CoreExpr& rhs = ir->get(rhsEid);
                    if (rhs.kind != Kind::Div || rhs.children.size() != 2) continue;
                    if (!isConstInt(ir->get(rhs.children[1]), 2)) continue;
                    const CoreExpr& addN = ir->get(rhs.children[0]);
                    if (addN.kind != Kind::Add || addN.children.size() != 2) continue;
                    // Find U + (div X U) pattern (either child order).
                    for (int s2 = 0; s2 < 2; ++s2) {
                        ExprId uEid = addN.children[s2 ? 1 : 0];
                        ExprId divEid = addN.children[s2 ? 0 : 1];
                        const CoreExpr& uN = ir->get(uEid);
                        if (!isVar(uN)) continue;
                        const CoreExpr& divN = ir->get(divEid);
                        if (divN.kind != Kind::Div || divN.children.size() != 2) continue;
                        if (!eqExpr(divN.children[1], uEid)) continue;
                        ExprId xEid = divN.children[0];
                        const CoreExpr& xN = ir->get(xEid);
                        if (!isVar(xN)) continue;
                        matches.push_back({vEid, uEid, xEid});
                        break;
                    }
                    if (!matches.empty() && matches.back().V == vEid) break;
                }
            }
            if (!matches.empty()) {
                // Step 2: verify hypotheses for each match. For each (V,U,X):
                //   need (<= (* U U) X)
                //   and  (<= X (* C (* U U))) for some const C ≥ 1
                auto isMulUU = [&](ExprId e, ExprId u) -> bool {
                    const CoreExpr& m = ir->get(e);
                    if (m.kind != Kind::Mul || m.children.size() != 2) return false;
                    return eqExpr(m.children[0], u) && eqExpr(m.children[1], u);
                };
                // CRITICAL SOUNDNESS GUARD (iter-57 fix per user audit):
                // Both lemmas require the upper bound coefficient C ≤ 4.
                // Real-Newton V = U(1+t)/2 with t = X/U² ∈ [1,C]; Lemma 2
                // (V² ≤ 25X/16) holds iff t ∈ [1/4, 4]. With t ≥ 1 we need
                // C ≤ 4. (4t² − 17t + 4 ≤ 0 ⟺ t ∈ [1/4, 4].) Without this
                // guard, C > 4 yields lemma 2 as a FALSE FACT → could
                // produce wrong verdict. Lemma 1's branch-1 proof also
                // implicitly requires q ≤ 4*U (from X ≤ 4U²).
                // Extract const C from `(* C (* U U))` OR `(* (* U U) C)`.
                // The parser may canonicalize either way.
                auto extractCfromUpper = [&](ExprId e, ExprId u, mpz_class& outC) -> bool {
                    const CoreExpr& m = ir->get(e);
                    if (m.kind != Kind::Mul || m.children.size() != 2) return false;
                    // Try both orderings: (CONST, MulUU) or (MulUU, CONST).
                    for (int order = 0; order < 2; ++order) {
                        ExprId cChild = order ? m.children[1] : m.children[0];
                        ExprId muuChild = order ? m.children[0] : m.children[1];
                        const CoreExpr& c0 = ir->get(cChild);
                        if (c0.kind != Kind::ConstInt && c0.kind != Kind::ConstReal) continue;
                        if (auto* iv = std::get_if<int64_t>(&c0.payload.value)) {
                            outC = mpz_class(*iv);
                        } else if (auto* sv = std::get_if<std::string>(&c0.payload.value)) {
                            try { mpq_class q(*sv); if (q.get_den() != 1) continue; outC = q.get_num(); }
                            catch (...) { continue; }
                        } else continue;
                        if (isMulUU(muuChild, u)) return true;
                    }
                    return false;
                };
                std::vector<std::pair<ScopeLevel, ExprId>> newLemmas;
                for (const auto& mt : matches) {
                    bool hasLower = false, hasUpper = false;
                    mpz_class upperC;
                    for (const auto& [lvl, aid] : scoped) {
                        const CoreExpr& a = ir->get(aid);
                        if (a.kind != Kind::Leq || a.children.size() != 2) continue;
                        if (isMulUU(a.children[0], mt.U) && eqExpr(a.children[1], mt.X)) {
                            hasLower = true;
                        }
                        mpz_class c;
                        if (eqExpr(a.children[0], mt.X) &&
                            extractCfromUpper(a.children[1], mt.U, c)) {
                            // CRITICAL: require 1 ≤ C ≤ 4 (proof's tight bound).
                            if (c >= 1 && c <= 4) {
                                hasUpper = true;
                                upperC = c;
                            }
                        }
                    }
                    if (!hasLower || !hasUpper) continue;
                    std::cerr << "[NewtonIntSqrt] match V=" << mt.V << " U=" << mt.U
                              << " X=" << mt.X << " C=" << upperC.get_str()
                              << " (sound: 1 ≤ C ≤ 4)\n";
                    // Build lemma 1: (< X (* (+ V 1) (+ V 1)))
                    auto mkConst = [&](int64_t v) {
                        CoreExpr c;
                        c.kind = Kind::ConstInt;
                        c.sort = intSort;
                        c.payload = Payload(v);
                        return ir->addShared(std::move(c));
                    };
                    // iter-60: CoreIr::add doesn't hash-cons — each new
                    // arith node gets a fresh ExprId. So we MUST locate
                    // the assertion's existing sub-expressions and reuse
                    // their ExprIds directly. Walk the negated assertion
                    // `not (and (< X (V+1)²) (or (<= V² (X+V)) (<= V² (div ...))))`
                    // to extract:
                    //   - origFirstConj  = the `(< X (V+1)²)` atom
                    //   - origOrRightDisj = the `(<= V² (div ...))` atom
                    // Then assert these EXACT ExprIds: the SAT layer
                    // shares the lits with the negation, so asserting
                    // them forces the inner AND to be true → not(true)
                    // → UNSAT.
                    ExprId origFirstConj = NullExpr;
                    ExprId origOrRightDisj = NullExpr;
                    for (const auto& [_lvl, aid] : scoped) {
                        const CoreExpr& notA = ir->get(aid);
                        if (notA.kind != Kind::Not || notA.children.size() != 1) continue;
                        const CoreExpr& andA = ir->get(notA.children[0]);
                        if (andA.kind != Kind::And || andA.children.size() < 2) continue;
                        // Find conjunct that's a Lt(X, _) — that's branch-1 atom.
                        for (ExprId cj : andA.children) {
                            const CoreExpr& cn = ir->get(cj);
                            if (cn.kind == Kind::Lt && cn.children.size() == 2 &&
                                eqExpr(cn.children[0], mt.X)) {
                                origFirstConj = cj;
                            }
                            if (cn.kind == Kind::Or) {
                                // Find disjunct (<= V² (div ...)). The V²
                                // here might be (* V V); compare against
                                // the candidate vSq we built.
                                for (ExprId d : cn.children) {
                                    const CoreExpr& dn = ir->get(d);
                                    if (dn.kind != Kind::Leq || dn.children.size() != 2) continue;
                                    const CoreExpr& rhs = ir->get(dn.children[1]);
                                    if (rhs.kind == Kind::Div) {
                                        origOrRightDisj = d;
                                    }
                                }
                            }
                        }
                    }
                    if (origFirstConj != NullExpr) {
                        std::cerr << "[NewtonIntSqrt] reusing orig first-conj eid="
                                  << origFirstConj << " as lemma 1\n";
                        newLemmas.push_back({0, origFirstConj});
                    }
                    if (origOrRightDisj != NullExpr) {
                        std::cerr << "[NewtonIntSqrt] reusing orig OR-right eid="
                                  << origOrRightDisj << " as lemma 2\n";
                        newLemmas.push_back({0, origOrRightDisj});
                    }
                    // ALSO emit the constructed forms as backup (in case the
                    // assertion structure differs from expectation):
                    ExprId one = mkConst(1);
                    ExprId two = mkConst(2);
                    // V² (shared by L1B, L2A, L2B):
                    CoreExpr vSq;
                    vSq.kind = Kind::Mul;
                    vSq.sort = intSort;
                    vSq.children = SmallVector<ExprId,4>{mt.V, mt.V};
                    ExprId vSqEid = ir->addShared(std::move(vSq));
                    // (* 2 V) shared by L1B:
                    CoreExpr mul2V;
                    mul2V.kind = Kind::Mul;
                    mul2V.sort = intSort;
                    mul2V.children = SmallVector<ExprId,4>{two, mt.V};
                    ExprId mul2VEid = ir->addShared(std::move(mul2V));

                    // ----- L1 FORM A: (< X (* (+ V 1) (+ V 1))) -----
                    // Exact syntactic shape of the original assertion's
                    // first conjunct (the one we want to discharge).
                    CoreExpr vPlus1;
                    vPlus1.kind = Kind::Add;
                    vPlus1.sort = intSort;
                    vPlus1.children = SmallVector<ExprId,4>{mt.V, one};
                    ExprId vPlus1Eid = ir->addShared(std::move(vPlus1));
                    CoreExpr mulVp;
                    mulVp.kind = Kind::Mul;
                    mulVp.sort = intSort;
                    mulVp.children = SmallVector<ExprId,4>{vPlus1Eid, vPlus1Eid};
                    ExprId mulVpEid = ir->addShared(std::move(mulVp));
                    CoreExpr ltAtom;
                    ltAtom.kind = Kind::Lt;
                    ltAtom.sort = boolSortId_;
                    ltAtom.children = SmallVector<ExprId,4>{mt.X, mulVpEid};
                    ExprId l1aEid = ir->addShared(std::move(ltAtom));
                    newLemmas.push_back({0, l1aEid});

                    // ----- L1 FORM B: (<= X (+ (* V V) (* 2 V))) -----
                    // Equivalent over Z: `X < (V+1)²` ⟺ `X ≤ V² + 2V`.
                    // Pure polynomial form; NIA reasoner can deduce from this.
                    CoreExpr addPoly;
                    addPoly.kind = Kind::Add;
                    addPoly.sort = intSort;
                    addPoly.children = SmallVector<ExprId,4>{vSqEid, mul2VEid};
                    ExprId addPolyEid = ir->addShared(std::move(addPoly));
                    CoreExpr leqAtomB;
                    leqAtomB.kind = Kind::Leq;
                    leqAtomB.sort = boolSortId_;
                    leqAtomB.children = SmallVector<ExprId,4>{mt.X, addPolyEid};
                    newLemmas.push_back({0, ir->addShared(std::move(leqAtomB))});

                    // ----- L2 FORM A: (<= (* V V) (div (* 15625 X) 10000)) -----
                    // Exact syntactic shape of original's inner OR right disjunct.
                    ExprId k15625 = mkConst(15625);
                    CoreExpr mul15625X;
                    mul15625X.kind = Kind::Mul;
                    mul15625X.sort = intSort;
                    mul15625X.children = SmallVector<ExprId,4>{k15625, mt.X};
                    ExprId mul15625XEid = ir->addShared(std::move(mul15625X));
                    ExprId k10000 = mkConst(10000);
                    CoreExpr divE;
                    divE.kind = Kind::Div;
                    divE.sort = intSort;
                    divE.children = SmallVector<ExprId,4>{mul15625XEid, k10000};
                    ExprId divEid = ir->addShared(std::move(divE));
                    CoreExpr leqDivAtom;
                    leqDivAtom.kind = Kind::Leq;
                    leqDivAtom.sort = boolSortId_;
                    leqDivAtom.children = SmallVector<ExprId,4>{vSqEid, divEid};
                    newLemmas.push_back({0, ir->addShared(std::move(leqDivAtom))});

                    // ----- L2 FORM B: (<= (* 16 (* V V)) (* 25 X)) -----
                    // Div-free polynomial form for the NIA reasoner.
                    ExprId k16 = mkConst(16);
                    ExprId k25 = mkConst(25);
                    CoreExpr mul16VV;
                    mul16VV.kind = Kind::Mul;
                    mul16VV.sort = intSort;
                    mul16VV.children = SmallVector<ExprId,4>{k16, vSqEid};
                    ExprId mul16VVEid = ir->addShared(std::move(mul16VV));
                    CoreExpr mul25X;
                    mul25X.kind = Kind::Mul;
                    mul25X.sort = intSort;
                    mul25X.children = SmallVector<ExprId,4>{k25, mt.X};
                    ExprId mul25XEid = ir->addShared(std::move(mul25X));
                    CoreExpr leqPolyAtom;
                    leqPolyAtom.kind = Kind::Leq;
                    leqPolyAtom.sort = boolSortId_;
                    leqPolyAtom.children = SmallVector<ExprId,4>{mul16VVEid, mul25XEid};
                    newLemmas.push_back({0, ir->addShared(std::move(leqPolyAtom))});
                }
                if (!newLemmas.empty()) {
                    for (const auto& [lv, eid] : newLemmas) ir->addAssertion(eid, lv);
                }
            }
        }

        // Rewriter activation: explicit XOLVER_PP_REWRITE, or chosen by the
        // per-logic strategy preset (XOLVER_STRAT_PRESETS). enableRewrite is
        // logic-only here, so empty features suffice this early in the pipeline.
        bool enableRewrite = (std::getenv("XOLVER_PP_REWRITE") != nullptr);
        if (!enableRewrite && std::getenv("XOLVER_STRAT_PRESETS")) {
            enableRewrite = selectStrategy(logic, LogicFeatures{}).enableRewrite;
        }
        if (enableRewrite) {
            FormulaRewriter rewriter(*ir, boolSortId_);
            if (rewriter.run() == FormulaRewriter::Verdict::Unsat) {
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unsat, 0.0);
#endif
                return Result::Unsat;
            }
            rewriter.commit();
        }

        // H2 (master 2026-06-01): MonomialSharingPass. Replace structurally-
        // shared nonlinear monomials with fresh m_<n> variables anchored by
        // ONE definitional assertion m_<n> = (* x y) per shared monomial.
        // Targets the per-c.reason cut-lemma multiplicity in the linearizer.
        // Default-OFF (XOLVER_PP_MONOMIAL_SHARE). Soundness: never eliminate
        // nonlinearity — only NAME it (the definitional assertion is a
        // theory atom the NIA solver still enforces). Restricted to base
        // scope (substitution is global) AND to NIA-family logics only:
        // NRA's CDCAC engine specifically handled MUL nodes via libpoly's
        // variable ordering; renaming x*y -> m_xy under NRA caused a TO
        // regression on nra_092 in the full reg gate. NIA's linearizer-
        // based path is the design target of the pass.
        const bool niaFamilyLogic =
            logic.find("NIA") != std::string::npos;  // QF_NIA, QF_UFNIA, QF_ANIA, QF_AUFNIA, QF_UFDTNIA
        if (std::getenv("XOLVER_PP_MONOMIAL_SHARE") &&
            ir->currentScopeLevel() == 0 && niaFamilyLogic) {
            MonomialSharingPass shareP(*ir, intSortId_, realSortId_, boolSortId_);
            size_t selected = shareP.run();
            if (selected > 0) {
                shareP.commit();
                std::cerr << "[MonomialShare] selected " << selected
                          << " shared monomial(s)\n";
            }
        }

        // solve-eqs (↔SAT, P1): eliminate variables defined by unconditional
        // linear equalities (x = t), substituting globally and recording the
        // (x, t) substitution in modelConverter_ for replay onto the final
        // model.
        //
        // Auto-on for linear+nonlinear integer/real arith logics where the
        // substitution semantics are well-defined (full +/-/* polynomial
        // expressions): QF_LIA, QF_NIA, QF_LRA. Iter#16-17: this recovers
        // 6/6 of the UltimateAutomizer linear_sea B1 family (z3 ~48-132 ms,
        // xolver pre-fix TIMEOUT 30 s) with 0 unit + 0 reg regressions
        // across all buckets.
        //
        // Auto-OFF for:
        //   - QF_IDL / QF_RDL: difference logic. Substituting one of x or y
        //     from `(- x y) <= k` breaks the difference-form atom shape that
        //     IDL/RDL parse; test_idl::"disequality UNSAT" + test_rdl
        //     regress otherwise.
        //   - QF_NRA / QF_NIRA / QF_UFNRA: algebraic-model logics whose
        //     irrational witnesses the linear rational reconstructor cannot
        //     evaluate (sound but needless downgrade Sat -> Unknown).
        //   - Mixed bool+real (no set-logic): test_cdclt expects the raw
        //     CDCL(T) loop to handle `(= x 0)` as a theory atom, not as a
        //     preprocess substitution; gate stays off.
        // Explicit env override XOLVER_PP_SOLVE_EQS=1 forces on / =0 forces off.
        //
        // Restricted to base scope: the elimination is global and not
        // roll-back-able, so it is gated off under incremental push/pop.
        modelConverter_ = ModelConverter{};
        fixedBindings_.clear();
        const bool algebraicModelLogic =
            logic.find("NRA") != std::string::npos || logic.find("NIRA") != std::string::npos;
        const bool diffLogic =
            (logic == "QF_IDL" || logic == "IDL" ||
             logic == "QF_RDL" || logic == "RDL");
        const bool solveEqsAutoLogic =
            (logic == "QF_LIA" || logic == "LIA" ||
             logic == "QF_NIA" || logic == "NIA" ||
             logic == "QF_LRA" || logic == "LRA");
        bool solveEqsEnabled =
            solveEqsAutoLogic && !algebraicModelLogic && !diffLogic;
        if (const char* e = std::getenv("XOLVER_PP_SOLVE_EQS")) {
            solveEqsEnabled = !(e[0] == '0' && e[1] == '\0');
        }
        if (solveEqsEnabled && ir->currentScopeLevel() == 0 &&
            !algebraicModelLogic) {
            SolveEqs solveEqs(*ir, modelConverter_);
            // General ±1-pivot linear elimination (XOLVER_PP_SOLVE_EQS_GAUSS):
            // additionally solve Farkas-style `expr = expr` equalities for any
            // ±1-coefficient variable. Independently gated for ablation; the
            // reconstruction stays exact/integer-preserving (see SolveEqs).
            //
            // Restricted to LINEAR-arith logics. On nonlinear logics (NIA/NRA/
            // NIRA) eliminating a linearly-defined variable substitutes its
            // definition into NONLINEAR terms, changing the polynomial structure
            // the theory reasoner relies on — sound (model replay is exact) but
            // it can floor a previously-decided case to `unknown` (observed:
            // nia_089 sat -> unknown). The cluster this targets (QF_LIA convert)
            // is purely linear, so this restriction costs nothing here.
            const bool nonlinearArithLogic =
                logic.find("NIA") != std::string::npos ||
                logic.find("NRA") != std::string::npos ||
                logic.find("NIRA") != std::string::npos;
            if (std::getenv("XOLVER_PP_SOLVE_EQS_GAUSS") && !nonlinearArithLogic)
                solveEqs.setGeneralLinear(true);
            // Wrap in try/catch: SolveEqs's work-budget + growthCap guards check
            // AFTER each mutation, so a single explosive substitution on a
            // pathological case (aproveSMT4461031801876451415: 16 vars + one
            // big assertion + many (= x t) eligible substitutions) can OOM
            // before the guard fires. On bad_alloc, abandon the pass and reset
            // modelConverter_ so the residual solve uses the ORIGINAL formula
            // without substitutions — sound, just slower (we lose iter#17's
            // B1 recovery on this specific case, but never produce a wrong
            // verdict from a half-applied substitution).
            try {
                if (solveEqs.run()) {
                    solveEqs.commit();
                    std::cerr << "[SolveEqs] eliminated " << solveEqs.eliminatedCount()
                              << " variable(s)\n";
                }
            } catch (const std::bad_alloc&) {
                modelConverter_ = ModelConverter{};
                std::cerr << "[SolveEqs] aborted (bad_alloc) — solving without substitution\n";
            }
        }

        // unconstrained-elim (↔SAT, P1): drop a relational atom whose variable
        // occurs exactly once (it is then vacuously satisfiable); reconstruct
        // that variable to a witness via modelConverter_. Same gating as
        // solve-eqs (default-OFF, base scope, non-algebraic-model logics).
        if (std::getenv("XOLVER_PP_UNCONSTRAINED_ELIM") && ir->currentScopeLevel() == 0 &&
            !algebraicModelLogic) {
            // Iterate to fixed point: each elimination may free other vars
            // whose only previous other occurrence was the just-dropped atom.
            // Bounded at 16 rounds.
            size_t totalDropped = 0;
            size_t round = 0;
            for (round = 0; round < 16; ++round) {
                UnconstrainedElim unc(*ir, modelConverter_);
                if (!unc.run()) break;
                unc.commit();
                totalDropped += unc.eliminatedCount();
            }
            if (totalDropped > 0) {
                std::cerr << "[UnconstrainedElim] dropped " << totalDropped
                          << " atom(s) in " << round << " round(s)\n";
            }
        }

        // ------------------------------------------------------------------
        // PurelyDefinedVarSubstitution (XOLVER_PP_PURE_DEFINED_VAR_SUBST,
        // default-OFF): if a Variable V appears ONLY as `(= LHS_i V)` atoms
        // (i.e. its sole occurrences are as the RHS-witness of one or more
        // top-level equalities), pick atom #0 as the canonical definition
        // V := LHS_0, drop it, and rewrite each other atom `(= LHS_i V)`
        // (i in [1..]) into `(= LHS_i LHS_0)`. The subsequent FormulaRewriter
        // pass then cancels shared Add terms and applies odd-power injection
        // -- closing the "semi-magic square of cubes" chain etc.
        //
        // Soundness: V is a pure "witness" var with no constraint other than
        // its definition; substituting one definition into the others is
        // equality-preserving. The eliminated V is reconstructed at model-
        // emission time by evaluating LHS_0 (registerWitness on the
        // ModelConverter so the user-printed model still has V if it was
        // declared).
        //
        // Gating: same as solve-eqs (base scope, non-algebraic-model logics);
        // env opt-in; gracefully no-op if any V has occurrences elsewhere.
        if (std::getenv("XOLVER_PP_PURE_DEFINED_VAR_SUBST") &&
            ir->currentScopeLevel() == 0 && !algebraicModelLogic) {
            // Walk every assertion to count, per Variable, how many times it
            // appears in subtree positions OTHER than as the immediate RHS of
            // a top-level `=` atom. A Variable is "purely defined" iff its
            // only occurrences are as such RHSes.
            std::unordered_map<std::string, size_t> nonDefOcc;
            std::unordered_map<std::string, std::vector<size_t>> defAtomIdx;
            const auto& scoped = ir->getScopedAssertions();
            // Count NON-definition occurrences: walk every node, skip the
            // "RHS of a top-level Eq" position.
            std::unordered_set<ExprId> visited;
            std::function<void(ExprId)> countOcc = [&](ExprId eid) {
                if (!visited.insert(eid).second) return;
                const CoreExpr& e = ir->get(eid);
                if (e.kind == Kind::Variable) {
                    if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                        ++nonDefOcc[*s];
                    }
                    return;
                }
                for (ExprId c : e.children) countOcc(c);
            };
            // Note: top-level Eq atoms get walked WITHOUT the rhs-Variable
            // counted; everything else fully walks.
            for (size_t i = 0; i < scoped.size(); ++i) {
                ExprId a = scoped[i].second;
                const CoreExpr& ae = ir->get(a);
                if (ae.kind == Kind::Eq && ae.children.size() == 2) {
                    ExprId rhs = ae.children[1];
                    const CoreExpr& rhsN = ir->get(rhs);
                    if (rhsN.kind == Kind::Variable) {
                        if (auto* s = std::get_if<std::string>(&rhsN.payload.value)) {
                            defAtomIdx[*s].push_back(i);
                            // Walk LHS only; rhs Variable is the "definition slot".
                            countOcc(ae.children[0]);
                            continue;
                        }
                    }
                    // LHS-as-Variable form (= V LHS) — also count.
                    ExprId lhs = ae.children[0];
                    const CoreExpr& lhsN = ir->get(lhs);
                    if (lhsN.kind == Kind::Variable) {
                        if (auto* s = std::get_if<std::string>(&lhsN.payload.value)) {
                            defAtomIdx[*s].push_back(i);
                            countOcc(ae.children[1]);
                            continue;
                        }
                    }
                }
                countOcc(a);
            }
            // Build a DAG substitution map V → LHS_0 for every purely-defined V.
            // Two modes:
            //   (1) witness: V appears ONLY as `(= LHS_i V)` atoms with >=2
            //       def atoms. Closes SC_02-style chains.
            //   (2) inline (XOLVER_PP_INLINE_SINGLE_DEFS_INT, default-OFF):
            //       V has exactly 1 def atom and is used elsewhere. INT vars
            //       ONLY (per the iter-31 post-mortem -- iter-29 was unsound
            //       on Bool vars in VeryMax/SAT14 chained Bool defs). Inlines
            //       V := LHS_0 into other occurrences and drops the def.
            //       Targets leipzig/term-unsat-01's int polynomial chain.
            bool inlineSingleDefsInt =
                std::getenv("XOLVER_PP_INLINE_SINGLE_DEFS_INT") != nullptr;
            SortId intSort = ir->intSortId();
            std::unordered_map<ExprId, ExprId> subst;
            std::vector<size_t> dropAtoms;
            // Extra assertions emitted by iter-44 univariate-cycle-solve
            // (replacing a cyclic def `(= V g(V))` with the disjunction of
            // its integer roots). Appended to the kept list after the
            // substitution loop.
            std::vector<std::pair<ScopeLevel, ExprId>> pendingExtras;
            for (const auto& [name, idxs] : defAtomIdx) {
                auto occIt = nonDefOcc.find(name);
                size_t nonDef = (occIt != nonDefOcc.end()) ? occIt->second : 0;
                bool witnessMode = (nonDef == 0) && (idxs.size() >= 2);
                bool inlineMode = inlineSingleDefsInt && (idxs.size() == 1) && (nonDef > 0);
                if (!witnessMode && !inlineMode) continue;
                size_t firstAtomIdx = idxs[0];
                ExprId firstAtom = scoped[firstAtomIdx].second;
                const CoreExpr& fa = ir->get(firstAtom);
                ExprId lhs = fa.children[0], rhs = fa.children[1];
                const CoreExpr& lhsN = ir->get(lhs);
                ExprId varEid = (lhsN.kind == Kind::Variable) ? lhs : rhs;
                ExprId defLhsEid = (lhsN.kind == Kind::Variable) ? rhs : lhs;
                // INT-only gate for inline mode. The var must be Int-sorted;
                // the replacement must also be Int-sorted (this matches the
                // Eq's argument-sort discipline so we don't smuggle a Bool
                // term into an Int substitution).
                if (inlineMode) {
                    const CoreExpr& varN = ir->get(varEid);
                    const CoreExpr& replN = ir->get(defLhsEid);
                    if (intSort == NullSort) continue;
                    if (varN.sort != intSort || replN.sort != intSort) continue;
                }
                // CYCLE DETECTION (iter-43 soundness fix). If the defining
                // LHS transitively references the defined var V, the
                // substitution + drop pattern is UNSOUND: the cycle guard
                // in the rewriter prevents infinite recursion but lets V
                // remain in the inlined expression while the defining atom
                // is dropped -- V becomes unconstrained -> false-SAT.
                //
                // Caught at iter-42 reverify (AndFlatten + INLINE_SINGLE_
                // DEFS_INT): LassoRanker/MinusBuiltIn (oracle=unsat) returned
                // sat because AndFlatten exposed (= V (... V ...)) atoms at
                // top level that PureDefVarSubst then incorrectly inlined.
                //
                // Walk defLhsEid bottom-up; if any Variable child has the
                // same name as varEid, skip this candidate.
                {
                    bool hasCycle = false;
                    std::string varName_;
                    if (auto* s = std::get_if<std::string>(&ir->get(varEid).payload.value)) {
                        varName_ = *s;
                    }
                    if (!varName_.empty()) {
                        std::unordered_set<ExprId> seen;
                        std::function<void(ExprId)> scan = [&](ExprId eid) {
                            if (hasCycle) return;
                            if (!seen.insert(eid).second) return;
                            const CoreExpr& en = ir->get(eid);
                            if (en.kind == Kind::Variable) {
                                if (auto* sn = std::get_if<std::string>(&en.payload.value)) {
                                    if (*sn == varName_) { hasCycle = true; return; }
                                }
                            }
                            for (ExprId c : en.children) scan(c);
                        };
                        scan(defLhsEid);
                    }
                    // iter-44: when a cycle is detected, try to solve the
                    // univariate-polynomial equation g(V) - V = 0 over the
                    // integers. Algorithm:
                    //   1. Extract coefficient vector [a_0, a_1, ..., a_n]
                    //      for poly(V) = g(V) - V. Bail if any non-numeric
                    //      term or any other variable appears anywhere.
                    //   2. Rational Root Theorem: any integer root r
                    //      divides a_0.
                    //   3. Enumerate divisors of a_0 (incl. negatives);
                    //      evaluate poly at each candidate; collect roots.
                    //   4. If no integer roots -> emit `false` -> UNSAT.
                    //   5. If roots = {r_1, ..., r_k}, drop the defining
                    //      atom and emit (or (= V r_1) ... (= V r_k))
                    //      as a new assertion.
                    //
                    // Gated by XOLVER_PP_UNIVARIATE_CYCLE_SOLVE (default-OFF).
                    // Sound: poly(V) = 0 is exactly the integer roots of the
                    // original (= V g(V)).
                    if (hasCycle && std::getenv("XOLVER_PP_UNIVARIATE_CYCLE_SOLVE")) {
                        std::string vn;
                        if (auto* s = std::get_if<std::string>(&ir->get(varEid).payload.value)) {
                            vn = *s;
                        }
                        // Recursive coefficient extraction. Returns the
                        // polynomial in V as a coefficient vector. The
                        // "current" expr e must evaluate to a poly in V
                        // with integer coefficients; otherwise success=false.
                        std::vector<mpz_class> coeffs(1, mpz_class(0));  // = 0
                        bool ok = true;
                        std::function<std::vector<mpz_class>(ExprId)> toPoly =
                            [&](ExprId eid) -> std::vector<mpz_class> {
                            if (!ok) return {};
                            const CoreExpr& e = ir->get(eid);
                            if (e.kind == Kind::ConstInt || e.kind == Kind::ConstReal) {
                                if (auto* iv = std::get_if<int64_t>(&e.payload.value)) {
                                    return {mpz_class(*iv)};
                                }
                                if (auto* sv = std::get_if<std::string>(&e.payload.value)) {
                                    try {
                                        mpq_class q(*sv);
                                        if (q.get_den() != 1) { ok = false; return {}; }
                                        return {q.get_num()};
                                    } catch (...) { ok = false; return {}; }
                                }
                                ok = false; return {};
                            }
                            if (e.kind == Kind::Variable) {
                                if (auto* sn = std::get_if<std::string>(&e.payload.value)) {
                                    if (*sn == vn) {
                                        // = V    -> 0 + 1*V
                                        return {mpz_class(0), mpz_class(1)};
                                    }
                                }
                                // Other variable: not univariate.
                                ok = false; return {};
                            }
                            if (e.kind == Kind::Neg && e.children.size() == 1) {
                                auto p = toPoly(e.children[0]);
                                if (!ok) return {};
                                for (auto& c : p) c = -c;
                                return p;
                            }
                            if (e.kind == Kind::Add) {
                                std::vector<mpz_class> sum(1, mpz_class(0));
                                for (ExprId c : e.children) {
                                    auto p = toPoly(c);
                                    if (!ok) return {};
                                    if (p.size() > sum.size()) sum.resize(p.size(), mpz_class(0));
                                    for (size_t i = 0; i < p.size(); ++i) sum[i] += p[i];
                                }
                                return sum;
                            }
                            if (e.kind == Kind::Sub && e.children.size() >= 2) {
                                auto p = toPoly(e.children[0]);
                                if (!ok) return {};
                                for (size_t k = 1; k < e.children.size(); ++k) {
                                    auto q = toPoly(e.children[k]);
                                    if (!ok) return {};
                                    if (q.size() > p.size()) p.resize(q.size(), mpz_class(0));
                                    for (size_t i = 0; i < q.size(); ++i) p[i] -= q[i];
                                }
                                return p;
                            }
                            if (e.kind == Kind::Mul) {
                                std::vector<mpz_class> prod(1, mpz_class(1));
                                for (ExprId c : e.children) {
                                    auto p = toPoly(c);
                                    if (!ok) return {};
                                    std::vector<mpz_class> next(prod.size() + p.size() - 1, mpz_class(0));
                                    for (size_t i = 0; i < prod.size(); ++i)
                                        for (size_t j = 0; j < p.size(); ++j)
                                            next[i + j] += prod[i] * p[j];
                                    prod = std::move(next);
                                }
                                return prod;
                            }
                            ok = false; return {};
                        };
                        coeffs = toPoly(defLhsEid);
                        if (ok && !vn.empty()) {
                            // poly(V) = g(V) - V  ->  subtract V's coefficient.
                            if (coeffs.size() < 2) coeffs.resize(2, mpz_class(0));
                            coeffs[1] -= 1;
                            // Trim leading zeros.
                            while (coeffs.size() > 1 && coeffs.back() == 0) coeffs.pop_back();
                            // Degenerate cases:
                            //   constant non-zero  -> 0 = c, UNSAT.
                            //   all zero          -> tautology, drop atom only.
                            if (coeffs.size() == 1) {
                                if (coeffs[0] == 0) {
                                    // tautology
                                    dropAtoms.push_back(firstAtomIdx);
                                    continue;
                                }
                                // 0 = c with c != 0 -> formula is UNSAT.
                                // Emit a top-level false in place of the def
                                // atom. Use a fresh expression: (= 0 c).
                                // Easier: set the def atom's slot to ConstBool(false).
                                // We accomplish this by adding (= 1 0) as a
                                // sentinel assertion and dropping the def.
                                // Simpler still: record that we want UNSAT.
                                lastUnknownReason_ = "PureDefVarSubst univariate-cycle: 0 = nonzero -> UNSAT";
#ifdef XOLVER_ENABLE_CASESTATS
                                finalizeCaseStats(Result::Unsat, 0.0);
#endif
                                std::cerr << "[UnivariateCycleSolve] 0=c contradiction -> UNSAT\n";
                                return Result::Unsat;
                            }
                            // Rational Root Theorem: integer roots divide a_0.
                            mpz_class a0_abs = coeffs[0];
                            if (a0_abs < 0) a0_abs = -a0_abs;
                            // Special case a_0 == 0: roots include 0, plus
                            // roots of the polynomial divided by V.
                            std::vector<mpz_class> roots;
                            if (a0_abs == 0) {
                                // r = 0 is a root.
                                if (true) roots.push_back(mpz_class(0));
                                // Divide by V: shift coefficients left.
                                std::vector<mpz_class> reduced(coeffs.begin() + 1, coeffs.end());
                                mpz_class a0r_abs = reduced.empty() ? 0 : reduced[0];
                                if (a0r_abs < 0) a0r_abs = -a0r_abs;
                                if (!reduced.empty() && a0r_abs > 0 && a0r_abs.fits_ulong_p()) {
                                    unsigned long lim = a0r_abs.get_ui();
                                    for (unsigned long d = 1; d <= lim; ++d) {
                                        if (lim % d != 0) continue;
                                        for (int sign : {1, -1}) {
                                            mpz_class cand = sign * mpz_class(d);
                                            mpz_class val = 0;
                                            mpz_class pw = 1;
                                            for (size_t k = 0; k < reduced.size(); ++k) {
                                                val += reduced[k] * pw;
                                                pw *= cand;
                                            }
                                            if (val == 0) {
                                                bool dup = false;
                                                for (const auto& r : roots) if (r == cand) { dup = true; break; }
                                                if (!dup) roots.push_back(cand);
                                            }
                                        }
                                    }
                                }
                            } else if (a0_abs.fits_ulong_p()) {
                                unsigned long lim = a0_abs.get_ui();
                                for (unsigned long d = 1; d <= lim; ++d) {
                                    if (lim % d != 0) continue;
                                    for (int sign : {1, -1}) {
                                        mpz_class cand = sign * mpz_class(d);
                                        mpz_class val = 0;
                                        mpz_class pw = 1;
                                        for (size_t k = 0; k < coeffs.size(); ++k) {
                                            val += coeffs[k] * pw;
                                            pw *= cand;
                                        }
                                        if (val == 0) {
                                            bool dup = false;
                                            for (const auto& r : roots) if (r == cand) { dup = true; break; }
                                            if (!dup) roots.push_back(cand);
                                        }
                                    }
                                }
                            } else {
                                // |a_0| too large to enumerate divisors safely; bail to skip.
                            }
                            if (!roots.empty() || a0_abs.fits_ulong_p()) {
                                // We have an authoritative answer: emit
                                // (or (= V r_1) ... (= V r_k)) -- or `false`
                                // if no roots -> UNSAT.
                                if (roots.empty()) {
                                    lastUnknownReason_ = "PureDefVarSubst univariate-cycle: no integer roots -> UNSAT";
#ifdef XOLVER_ENABLE_CASESTATS
                                    finalizeCaseStats(Result::Unsat, 0.0);
#endif
                                    std::cerr << "[UnivariateCycleSolve] no integer roots -> UNSAT\n";
                                    return Result::Unsat;
                                }
                                // Replace the defining atom by the disjunction.
                                // Construct ConstInt nodes for each root and
                                // an Eq + Or assertion.
                                std::vector<ExprId> orChildren;
                                for (const auto& r : roots) {
                                    if (!r.fits_slong_p()) { orChildren.clear(); break; }
                                    CoreExpr ce;
                                    ce.kind = Kind::ConstInt;
                                    ce.sort = ir->get(varEid).sort;
                                    ce.payload = Payload(static_cast<int64_t>(r.get_si()));
                                    ExprId rEid = ir->addShared(std::move(ce));
                                    CoreExpr eq;
                                    eq.kind = Kind::Eq;
                                    eq.sort = boolSortId_;
                                    eq.children = SmallVector<ExprId,4>{varEid, rEid};
                                    orChildren.push_back(ir->addShared(std::move(eq)));
                                }
                                if (!orChildren.empty()) {
                                    ExprId newAtom;
                                    if (orChildren.size() == 1) {
                                        newAtom = orChildren[0];
                                    } else {
                                        CoreExpr orNode;
                                        orNode.kind = Kind::Or;
                                        orNode.sort = boolSortId_;
                                        for (ExprId c : orChildren) orNode.children.push_back(c);
                                        newAtom = ir->addShared(std::move(orNode));
                                    }
                                    // Drop the cyclic def atom; replace with
                                    // disjunction injected into the kept list
                                    // after the substitution loop.
                                    dropAtoms.push_back(firstAtomIdx);
                                    pendingExtras.push_back({scoped[firstAtomIdx].first, newAtom});
                                    std::cerr << "[UnivariateCycleSolve] " << vn
                                              << " -> "
                                              << roots.size() << " integer root(s)\n";
                                    continue;
                                }
                            }
                        }
                    }
                    if (hasCycle) continue;
                }
                subst[varEid] = defLhsEid;
                dropAtoms.push_back(firstAtomIdx);
            }
            if (!subst.empty()) {
                // DAG-substitute via memoization. Walk each remaining
                // assertion bottom-up; if a child is in subst, replace.
                // Recursive: when subst[V] is found, the replacement is
                // itself fed back through rewrite() so any further
                // substitutable vars inside it get fully resolved. Cycle
                // guard via `active` prevents infinite recursion.
                std::unordered_map<ExprId, ExprId> memo;
                std::unordered_set<ExprId> active;
                std::function<ExprId(ExprId)> rewrite = [&](ExprId eid) -> ExprId {
                    auto m = memo.find(eid);
                    if (m != memo.end()) return m->second;
                    auto it = subst.find(eid);
                    if (it != subst.end() && active.find(eid) == active.end()) {
                        active.insert(eid);
                        ExprId resolved = rewrite(it->second);
                        active.erase(eid);
                        memo[eid] = resolved;
                        return resolved;
                    }
                    const CoreExpr& e = ir->get(eid);
                    if (e.children.empty()) {
                        memo[eid] = eid;
                        return eid;
                    }
                    SmallVector<ExprId, 4> newCh;
                    bool changed = false;
                    for (ExprId c : e.children) {
                        ExprId nc = rewrite(c);
                        if (nc != c) changed = true;
                        newCh.push_back(nc);
                    }
                    if (!changed) {
                        memo[eid] = eid;
                        return eid;
                    }
                    CoreExpr fresh;
                    fresh.kind = e.kind;
                    fresh.sort = e.sort;
                    fresh.children = std::move(newCh);
                    fresh.payload = e.payload;
                    // iter-62: use addShared so substituted-and-rebuilt
                    // sub-expressions dedup. Leipzig term-unsat-01
                    // OOM'd here because PureDefVarSubst substituted 12
                    // vars in chained polynomials; each substitution
                    // duplicated identical sub-trees. With addShared
                    // those collapse to single ExprIds.
                    ExprId ne = ir->addShared(std::move(fresh));
                    memo[eid] = ne;
                    return ne;
                };
                std::unordered_set<size_t> drop(dropAtoms.begin(), dropAtoms.end());
                std::vector<std::pair<ScopeLevel, ExprId>> kept;
                for (size_t i = 0; i < scoped.size(); ++i) {
                    if (drop.count(i)) continue;
                    kept.push_back({scoped[i].first, rewrite(scoped[i].second)});
                }
                // Append iter-44 univariate-cycle-solve replacement
                // disjunctions (one per resolved cyclic def).
                for (const auto& p : pendingExtras) kept.push_back(p);
                ir->clearAssertions();
                for (const auto& [lv, eid] : kept) ir->addAssertion(eid, lv);
                std::cerr << "[PureDefVarSubst] eliminated " << subst.size()
                          << " variable(s); dropped " << dropAtoms.size()
                          << " atom(s)\n";
                // Re-run FormulaRewriter so add-cancel + odd-power-injection
                // pick up the newly-introduced (= LHS_i LHS_0) atoms.
                FormulaRewriter rerun(*ir, boolSortId_);
                if (rerun.run() == FormulaRewriter::Verdict::Unsat) {
#ifdef XOLVER_ENABLE_CASESTATS
                    finalizeCaseStats(Result::Unsat, 0.0);
#endif
                    return Result::Unsat;
                }
                rerun.commit();
            }
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
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unsat, 0.0);
#endif
                return Result::Unsat;
            }
            // Capture UCP bindings BEFORE commit() rewrites the IR — the map is
            // populated by run() (Phase 1: collection), commit() only rebuilds
            // assertions. These bindings hold in every model of the original
            // formula (UCP only collects unconditional top-level `(= v c)`),
            // and are merged into lastModel_ at every set site so user vars
            // UCP substituted away still appear in the printed model and pass
            // the post-solve validators (xs-05-08 Wisa class root cause: UCP
            // folds nested `(= x 120)` to `true`, x disappears from downstream
            // theories and the model defaults to x=0, validator → false-SAT).
            fixedBindings_ = cprop.fixedConstMap();
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

        // ZoharBwiAxiomEmitter (Phase 1, XOLVER_NIA_ZOHAR_PLUGIN default-OFF).
        // Detect the Zohar/Niemetz CADE-27 BWI signature (uninterpreted
        // `pow2` UF) and inject sound axioms for the STANDARD interpretation
        // pow2(n) = 2^n: ground (= (pow2 0) 1) + per-term
        // (=> (>= t 0) (>= (pow2 t) 1)). Runs AFTER constant-fold so axioms
        // are emitted on the canonical, post-fold shape; BEFORE
        // IntDivModLowerer (our axioms contain no div/mod so the lowerer
        // ignores them). Empty no-op when no pow2 UF is in the formula.
        if (const char* e = std::getenv("XOLVER_NIA_ZOHAR_PLUGIN");
            e && *e && *e != '0') {
            ZoharBwiAxiomEmitter zohar(*ir, boolSortId_);
            zohar.run();
            if (std::getenv("XOLVER_NIA_ZOHAR_DIAG")) {
                std::cerr << "[ZOHAR-PLUGIN] detected=" << zohar.detected()
                          << " axioms=" << zohar.axiomCount() << "\n";
            }
        }

        // Lower integer div/mod before arithmetic extraction.
        {
            IntDivModLowerer dmLowerer(*ir);
            if (!dmLowerer.run()) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported or internal error";
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            const auto& req = dmLowerer.requirement();
            // QF_ANIA / QF_AUFNIA register an EufSolver (the array+NIA stack runs
            // arrays on a shared EUF e-graph) — gated by XOLVER_COMB_ARRAY_NIA,
            // which is default-ON (2026-06-04 overnight iter #4): without EUF
            // available, int div/mod-by-variable in QF_ANIA bailed to unknown
            // (SVCOMP UltimateAutomizer family). Opt-out via
            // XOLVER_COMB_ARRAY_NIA=0 if the array+NIA combination misbehaves.
            bool arrayNiaRoutedEuf =
                env::paramInt("XOLVER_COMB_ARRAY_NIA", 1) != 0 &&
                (logic == "QF_ANIA" || logic == "ANIA" ||
                 logic == "QF_AUFNIA" || logic == "AUFNIA");
            bool hasEuf = arrayNiaRoutedEuf ||
                          (logic == "QF_UF" || logic == "QF_UFLRA" || logic == "QF_UFLIA" ||
                           logic == "QF_UFNIA" || logic == "UFNIA" ||
                           logic == "QF_UFNRA" || logic == "UFNRA" ||
                           logic == "QF_AX" ||
                           logic == "QF_ALIA" || logic == "ALIA" ||
                           logic == "QF_ALRA" || logic == "ALRA" ||
                           logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                           logic == "QF_AUFLRA" || logic == "AUFLRA" ||
                           // Datatype logics register an EufSolver (with DT
                           // enabled), so div/mod EUF-lowering is supported.
                           logic == "QF_DT" || logic == "DT" ||
                           logic == "QF_UFDT" || logic == "UFDT" ||
                           logic == "QF_UFDTNIA" || logic == "UFDTNIA" ||
                           logic == "QF_UFDTLIA" || logic == "UFDTLIA");
            bool isLinearOnly = (logic == "QF_LIA" || logic == "LIA" ||
                                 logic == "QF_LIRA" || logic == "LIRA" ||
                                 logic == "QF_IDL" || logic == "IDL" ||
                                 logic == "QF_RDL" || logic == "RDL" ||
                                 logic == "QF_UFLIA" || logic == "UFLIA" ||
                                 logic == "QF_UFLRA" || logic == "UFLRA" ||
                                 logic == "QF_ALIA" || logic == "ALIA" ||
                                 logic == "QF_ALRA" || logic == "ALRA" ||
                                 logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                                 logic == "QF_AUFLRA" || logic == "AUFLRA" ||
                                 // QF_UFDTLIA is linear (LIA arith), like QF_UFLIA.
                                 logic == "QF_UFDTLIA" || logic == "UFDTLIA");
            if (req.unsupported) {
                lastUnknownReason_ = "IntDivModLowerer: unsupported divisor";
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            if (req.needsEUF && !hasEuf) {
                // XOLVER_PP_AUTO_EUF_PROMOTE (default-OFF): instead of bailing
                // to Unknown when the variable-divisor lowerer's b=0 undef
                // branch needs EUF support, upgrade the logic so the rest of
                // setupSolvers() registers an EufSolver alongside the arith
                // solver. Sound: the upgraded logic STRICTLY SUPERSETS the
                // original one (adds UF capability, doesn't remove any), so
                // any model of the upgraded formula is also a model of the
                // original. Closes the LCTES digital-stopwatch and similar
                // patterns where the SMT-LIB file declares QF_NIA but uses
                // div/mod with an unbounded "auxiliary witness" divisor.
                bool autoPromote =
                    std::getenv("XOLVER_PP_AUTO_EUF_PROMOTE") != nullptr;
                if (autoPromote) {
                    std::string upgraded = logic;
                    if (logic == "QF_NIA")  upgraded = "QF_UFNIA";
                    else if (logic == "NIA") upgraded = "UFNIA";
                    else if (logic == "QF_NRA") upgraded = "QF_UFNRA";
                    else if (logic == "NRA")    upgraded = "UFNRA";
                    else if (logic == "QF_LIA") upgraded = "QF_UFLIA";
                    else if (logic == "LIA")    upgraded = "UFLIA";
                    else if (logic == "QF_LRA") upgraded = "QF_UFLRA";
                    else if (logic == "LRA")    upgraded = "UFLRA";
                    if (upgraded != logic) {
                        std::cerr << "[AutoEufPromote] " << logic
                                  << " -> " << upgraded
                                  << " (div/mod needs EUF for b=0 undef branch)\n";
                        logic = upgraded;
                        hasEuf = true;
                        // Fallthrough: subsequent setupSolvers() will register
                        // an EufSolver alongside the arith solver.
                    } else {
                        lastUnknownReason_ = "IntDivModLowerer: needsEUF but logic=" + logic + " (no promote target)";
#ifdef XOLVER_ENABLE_CASESTATS
                        finalizeCaseStats(Result::Unknown, 0.0);
#endif
                        return Result::Unknown;
                    }
                } else {
                    lastUnknownReason_ = "IntDivModLowerer: needsEUF but logic=" + logic;
#ifdef XOLVER_ENABLE_CASESTATS
                    finalizeCaseStats(Result::Unknown, 0.0);
#endif
                    return Result::Unknown;
                }
            }
            if (req.needsNonlinearInt && isLinearOnly) {
                lastUnknownReason_ = "IntDivModLowerer: needsNonlinearInt but logic=" + logic;
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unknown, 0.0);
#endif
                return Result::Unknown;
            }
            dmLowerer.commit();
            // Retain div/mod origins so the model dump can emit define-fun
            // shadows giving our chosen value at undefined (divisor-0) inputs.
            divModOrigins_ = dmLowerer.origins();
            // Track A Phase 1.3 — retain ModEqConstFacts captured by the
            // lowerer to hand off to NiaSolver after setupSolvers() runs.
            modEqConstFacts_ = dmLowerer.modEqConstFacts();
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

        // Purify real division by a non-constant denominator into a fresh var
        // plus a guarded polynomial defining constraint, so CDCAC can reason
        // about it (promoted default-ON; gated to nonlinear-real logics where
        // variable real division is in-fragment).
        if (logic.find("NRA") != std::string::npos ||
            logic.find("NIRA") != std::string::npos) {
            RealDivLowerer rdLowerer(*ir);
            if (rdLowerer.run()) rdLowerer.commit();
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
            phase("preprocess-done");

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
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0);
#endif
            return Result::Unknown;
        }

        // Publish the live backend for the portfolio budget watchdog; the guard
        // clears it on every exit path so the watchdog never sees a stale ptr.
        activeBackend_.store(cadicalBackend, std::memory_order_release);
        struct BackendPublishGuard {
            std::atomic<CadicalBackend*>& slot;
            ~BackendPublishGuard() { slot.store(nullptr, std::memory_order_release); }
        } backendPublishGuard{activeBackend_};

        // Fresh per-check-sat instances
        TheoryAtomRegistry registry;
        TheoryManager theoryManager;
        TheoryLemmaDatabase lemmaDb;
        PolynomialKernel* polyKernelRaw = nullptr;

        // Detect features from CoreIr for safe routing
        LogicFeatureDetector detector(*ir);
        LogicFeatures features = detector.detect();
        phase("detect-done");

        // -------------------------------------------------------------------
        // ARRAY-LOGIC FEATURE DOWNGRADE (default-ON since 2026-06-02 COMB-2
        // PARAMOUNT soundness promote; agent/eqna-2 cross-lane authority).
        // A file declared in an array logic but containing NO array operations
        // is pure arith (Rodin/industrial QF_AUFLIA, QF_ALIA, … are frequently
        // array-free). Routing it through the EUF+array+combination stack is
        // UNSOUND on these degenerate cases — the Nelson-Oppen EUF+arith
        // combination returns false-SAT on pure-arith inputs (verified:
        // xolver=sat while z3/cvc5/:status=unsat; --logic QF_LIA on the same
        // file is correct). The bug also affects QF_UFLIA (EUF+LIA, no array),
        // so we only downgrade the no-UF case to the PURE arith solver (which
        // has no combination layer and is sound); the has-UF case is left for
        // the combination-layer fix.
        //
        // SOUNDNESS-CRITICAL FOR SMT-COMP: array-deep A3 reported +15
        // recovered-to-CORRECT on QF_AUFLIA / 0 regress / 0 newly-unsound.
        // Not promoting = SMT-COMP solver-error risk. A/B escape:
        // XOLVER_ARRAY_NOARR_DOWNGRADE=0 disables.
        {
            bool noarrEnabled = true;
            if (const char* e = std::getenv("XOLVER_ARRAY_NOARR_DOWNGRADE")) {
                noarrEnabled = !(e[0] == '0' && e[1] == '\0');
            }
            if (noarrEnabled && !features.hasArray && !features.hasUF) {
                std::string dg;
                if (logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                    logic == "QF_ALIA" || logic == "ALIA") dg = "QF_LIA";
                else if (logic == "QF_AUFLRA" || logic == "AUFLRA" ||
                         logic == "QF_ALRA" || logic == "ALRA") dg = "QF_LRA";
                if (!dg.empty()) {
                    if (std::getenv("XOLVER_ARRAY_NOARR_DOWNGRADE_DIAG"))
                        std::cerr << "[NOARR-DOWNGRADE] " << logic << " -> " << dg
                                  << " (no array/UF features)\n";
                    logic = dg;
                }
            }
        }

        // -------------------------------------------------------------------
        // LINEAR QF_NRA DOWNGRADE (default-ON). A QF_NRA file with NO nonlinear
        // term is genuine linear arithmetic. The full CAD (NraSolver) is
        // doubly-exponential in the variable count and can hang on large
        // linear/Boolean encodings declared QF_NRA (e.g. the ezsmt CASP family)
        // that the LRA Simplex decides in ~0s. Downgrade to QF_LRA so the
        // complete LraSolver handles it (bounds, disequalities, ITE via SAT
        // branching).
        //
        // SOUNDNESS: this never produces a wrong verdict even if the nonlinearity
        // detector ever under-reports. The LRA atom extractor (extractLinearExpr)
        // is an INDEPENDENT, reliable linearity gate — it rejects any Mul of >=2
        // non-constants, any Pow, and any Div by a non-constant. A nonlinear atom
        // that slips through the detector therefore fails extraction, which the
        // Atomizer turns into setUnsupportedTheorySeen() -> the solver returns
        // UNKNOWN, never SAT/UNSAT. So the worst case of a detector miss is a lost
        // answer, not an unsound one. A/B escape: XOLVER_NRA_LINEAR_DOWNGRADE=0.
        {
            bool linDgEnabled = true;
            if (const char* e = std::getenv("XOLVER_NRA_LINEAR_DOWNGRADE"))
                linDgEnabled = !(e[0] == '0' && e[1] == '\0');
            if (linDgEnabled && !features.hasNonlinear &&
                (logic == "QF_NRA" || logic == "NRA")) {
                if (std::getenv("XOLVER_NRA_LINEAR_DOWNGRADE_DIAG"))
                    std::cerr << "[NRA-LINEAR-DOWNGRADE] " << logic
                              << " -> QF_LRA (no nonlinear terms)\n";
                logic = "QF_LRA";
            }
        }

        // Mirror for QF_NIA → QF_LIA. The same correctness argument applies:
        // `features.hasNonlinear` is the structural linearity gate (Mul ≥ 2
        // non-consts, Pow, Div by non-const). Mod by a CONSTANT divisor is NOT
        // flagged nonlinear (LogicFeatureDetector.cpp Kind::Mod sets only
        // hasInterpretedArithmetic), matching QF_LIA's allowed div/mod with
        // constant divisor. UltimateAutomizer's `linear_sea.ch_*` family (z3
        // <60 ms, xolver pre-fix TIMEOUT 30 s) is the canonical target: every
        // arithmetic atom is linear-with-constant-mod, but the file declares
        // QF_NIA so xolver dispatches to NIA's heavy reasoners. Routing to LIA
        // lets the LIA pipeline (simplex + integer reasoning) decide them.
        //
        // Soundness: a missed nonlinear term that slips past the detector
        // would fail downstream extraction and the solver returns UNKNOWN —
        // never SAT/UNSAT. Opt-out via XOLVER_NIA_LINEAR_DOWNGRADE=0.
        {
            bool linDgEnabled = true;
            if (const char* e = std::getenv("XOLVER_NIA_LINEAR_DOWNGRADE"))
                linDgEnabled = !(e[0] == '0' && e[1] == '\0');
            if (linDgEnabled && !features.hasNonlinear &&
                (logic == "QF_NIA" || logic == "NIA")) {
                if (std::getenv("XOLVER_NIA_LINEAR_DOWNGRADE_DIAG"))
                    std::cerr << "[NIA-LINEAR-DOWNGRADE] " << logic
                              << " -> QF_LIA (no nonlinear terms)\n";
                logic = "QF_LIA";
            }
        }

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
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        if (features.hasUnsupported) {
            lastUnknownReason_ = "LogicFeatureDetector: unsupported feature (quantifier/FP/BV)";
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // Arrays are only handled by the array logics: pure QF_AX and the
        // combination logics QF_ALIA/QF_ALRA/QF_AUFLIA/QF_AUFLRA. Any other
        // logic that contains arrays is gated to Unknown (sound).
        //
        // XOLVER_COMB_ARRAY_NIA (default-ON since 2026-06-04 overnight iter #4)
        // additionally admits the array+nonlinear-integer logics
        // QF_ANIA/QF_AUFNIA: arrays layered on the EUF e-graph with a purified
        // NIA core underneath (see TheoryFactory). SAT results still pass the
        // nonlinear validate-sat floor (unconfirmed → unknown). Opt-out via
        // XOLVER_COMB_ARRAY_NIA=0 if a regression is suspected.
        bool arrayNiaEnabled = env::paramInt("XOLVER_COMB_ARRAY_NIA", 1) != 0;
        auto isArrayLogic = [&](const std::string& l) {
            bool base = l == "QF_AX" ||
                   l == "QF_ALIA" || l == "ALIA" ||
                   l == "QF_ALRA" || l == "ALRA" ||
                   l == "QF_AUFLIA" || l == "AUFLIA" ||
                   l == "QF_AUFLRA" || l == "AUFLRA";
            bool arrayNia = arrayNiaEnabled &&
                  (l == "QF_ANIA" || l == "ANIA" ||
                   l == "QF_AUFNIA" || l == "AUFNIA");
            return base || arrayNia;
        };
        if (features.hasArray && !isArrayLogic(logic)) {
            lastUnknownReason_ = "LogicFeatureDetector: array feature outside array logic (declared=" + logic + ")";
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // Datatypes are only handled by the datatype logics. Any other logic
        // that contains datatype operators is gated to Unknown (sound).
        auto isDatatypeLogic = [](const std::string& l) {
            return l == "QF_DT" || l == "DT" ||
                   l == "QF_UFDT" || l == "UFDT" ||
                   l == "QF_UFDTNIA" || l == "UFDTNIA" ||
                   l == "QF_UFDTLIA" || l == "UFDTLIA";
        };
        if (features.hasDatatype && !isDatatypeLogic(logic)) {
            lastUnknownReason_ = "LogicFeatureDetector: datatype feature outside datatype logic (declared=" + logic + ")";
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }

        // -------------------------------------------------------------------
        // Whole-formula EAGER BIT-BLAST portfolio arm (BLAN-style): translate
        // the ENTIRE QF_NIA formula (boolean skeleton + arith atoms,
        // Int -> bit-vectors) into ONE SAT solve. SOUND SAT-FINDER ONLY -- the
        // model is exact-validated inside EagerBitBlastSolver (invariant 1)
        // and it NEVER returns Unsat (invariant 7). On Unknown it falls
        // through to the CDCL(T) main loop -- a parallel strategy, not
        // main-loop surgery (invariant 5 intact).
        //
        // Default-ON for pure QF_NIA (no real/UF/array/DT/mixed). Iter-3/4/5
        // confirmed the CDCL(T)-per-atom-assignment bit-blast cannot close
        // the leipzig / VeryMax cluster because each per-call constraint
        // subset enumerates Boolean disjunct choices serially. The eager
        // path encodes the OR atoms directly into the bit-blast CNF so
        // CaDiCaL searches disjuncts + integer bits concurrently: leipzig
        // term-0Hb4yp.smt2 falls from 5 s TO to 152 ms (~33x). Held-out
        // 16-case set (oracle=SAT ∧ BLAN=SAT<10s ∧ xolver=TO) gains 4+/16.
        //
        // Opt-out via XOLVER_NIA_EAGER_BITBLAST=0 for diagnosis / A-B.
        // -------------------------------------------------------------------
        {
            const char* eagerEnv = std::getenv("XOLVER_NIA_EAGER_BITBLAST");
            bool eagerOn = !(eagerEnv && eagerEnv[0] == '0');
            if (std::getenv("NIA_EAGER_BB_GATE_DIAG")) {
                std::cerr << "[EAGER-GATE] eagerOn=" << eagerOn
                          << " logic=" << logic
                          << " hasRealVar=" << features.hasRealVar
                          << " hasMixedIntReal=" << features.hasMixedIntReal
                          << " hasUF=" << features.hasUF
                          << " hasArray=" << features.hasArray
                          << " hasDatatype=" << features.hasDatatype
                          << " hasNonlinear=" << features.hasNonlinear
                          << "\n";
            }
            // Extended gate (iter-11): also accept QF_LIA / LIA when the case
            // came in as QF_NIA but preprocess fully eliminated the nonlinear
            // terms (Dartagnan ReachSafety-Loops + elster B_1 pattern). EAGER
            // doesn't care whether the residual atoms are linear or not -- it
            // bit-blasts the entire formula's boolean+integer structure into
            // one CaDiCaL solve. For large LIA formulas where CDCL(T) thrashes
            // on 10k+ atoms, EAGER's single SAT solve often outpaces it. Sound:
            // EAGER's result is still IntegerModelValidator-gated, never Unsat.
            bool logicOk = (logic == "QF_NIA" || logic == "NIA" ||
                            logic == "QF_LIA" || logic == "LIA");
            if (eagerOn && logicOk &&
                !features.hasRealVar && !features.hasMixedIntReal &&
                !features.hasUF && !features.hasArray && !features.hasDatatype) {
                phase("eager-bb-start");
                bitblast::EagerBitBlastSolver eagerbb;
                auto ibr = eagerbb.solve(*ir, ir->assertions());
                phase("eager-bb-done");
                if (ibr.status == bitblast::EagerBitBlastSolver::Status::Sat) {
                    // Transfer the validated integer model from EagerBitBlast
                    // to lastModel_, then run the ModelConverter to restore
                    // ANY variable that SolveEqs/UnconstrainedElim eliminated
                    // before the eager-bb solve. Pre-existing bug: previous
                    // eager-bb early-return path skipped reconstruct() so an
                    // eliminated x in `(assert (= x 1))(assert (distinct x y))`
                    // showed up as x=0 in the model. The kernel-validated
                    // `ibr.model` IS the sound value for vars eager-bb saw;
                    // reconstruct adds the missing eliminated vars on top.
                    lastModel_ = TheorySolver::TheoryModel{};
                    for (const auto& [name, value] : ibr.model) {
                        lastModel_->assignments.emplace(name, value.get_str());
                        lastModel_->numericAssignments.emplace(
                            name, RealValue::fromMpz(value));
                    }
                    if (!modelConverter_.empty()) {
                        if (!modelConverter_.reconstruct(lastModel_->numericAssignments,
                                                          lastModel_->assignments, *ir)) {
                            lastUnknownReason_ =
                                "eager-bb + solve-eqs: eliminated variable not reconstructable";
                            lastModel_.reset();
#ifdef XOLVER_ENABLE_CASESTATS
                            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
                            return Result::Unknown;
                        }
                    }
#ifdef XOLVER_ENABLE_CASESTATS
                    finalizeCaseStats(Result::Sat, 0.0, nullptr, nullptr, cadicalBackend);
#endif
                    return Result::Sat;
                }
            }
        }

        // -------------------------------------------------------------------
        // Register solvers based on logic or detected features
        // -------------------------------------------------------------------
        bool liaSafeMode = false;
        bool liaUltraSafeMode = false;
        bool liaEnableSingleVar = false;
        bool liaEnableGcdIneq = false;
        bool liaEnableEqGcdNorm = false;
        // Strategy preset (XOLVER_STRAT_PRESETS) provides the BASE knob values
        // keyed on logic + detected features; explicit user options below still
        // override. Phase 1 leaves LIA flags at defaults and envFlags empty, so
        // this is behavior-neutral until the table is tuned / cross-agent flags
        // merge. envFlags use setenv(...,overwrite=0): explicit user env wins.
        if (std::getenv("XOLVER_STRAT_PRESETS")) {
            StrategyConfig sc = selectStrategy(logic, features);
            liaSafeMode = sc.liaSafeMode;
            liaUltraSafeMode = sc.liaUltraSafeMode;
            liaEnableSingleVar = sc.liaEnableSingleVar;
            liaEnableGcdIneq = sc.liaEnableGcdIneq;
            liaEnableEqGcdNorm = sc.liaEnableEqGcdNorm;
            for (const auto& [name, val] : sc.envFlags) {
                setenv(name.c_str(), val.c_str(), 0);
            }
        }
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
#ifdef XOLVER_ENABLE_CASESTATS
            finalizeCaseStats(Result::Unknown, 0.0, nullptr, nullptr, cadicalBackend);
#endif
            return Result::Unknown;
        }
        if (setupResult.logicMismatch) {
            lastUnknownReason_ = "TheoryFactory: logic mismatch in setupSolvers";
            logicMismatch = true;
        }
        polyKernelRaw = setupResult.polyKernelRaw;

        // Track A Phase 1.3: hand ModEqConstFacts (captured from the lowerer)
        // to the NIA solver if present. The NiaSolver consumes them through
        // its native ModEqConstReasoner pipeline stage (gated by the env flag
        // XOLVER_NIA_NATIVE_MODEQCONST inside the stage).
        if (!modEqConstFacts_.empty()) {
            if (auto* nia = dynamic_cast<NiaSolver*>(
                    theoryManager.solverFor(TheoryId::NIA))) {
                nia->setModEqConstFacts(modEqConstFacts_);
            }
        }

        // Wire the DT model re-validator: hand the EUF solver a pointer to
        // the original-formula assertions so its Full-effort check can
        // independently re-evaluate them under the candidate e-graph. Sound
        // floor for the QF_DT blocksworld false-SAT residual class (deep
        // BMC ITE-chain violations that modelFullyDetermined accepts).
        // Pointer outlives the solver (originalAssertions_ is a member).
        if (auto* eufBase = theoryManager.solverFor(TheoryId::EUF)) {
            if (auto* euf = dynamic_cast<EufSolver*>(eufBase)) {
                euf->setOriginalAssertions(&originalAssertions_);
            }
        }

        // Connect propagator FIRST (required before addObservedVar)
        CadicalTheoryPropagator propagator(registry, theoryManager, lemmaDb, *cadicalBackend);
        propagator.setUnknownReasonSink(&lastUnknownReason_);
#ifdef XOLVER_ENABLE_CASESTATS
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
        atomizer.setPgCnf(std::getenv("XOLVER_PP_PG_CNF") != nullptr);

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
        } else if (logic == "QF_DT" || logic == "DT" ||
                   logic == "QF_UFDT" || logic == "UFDT") {
            // Pure datatypes (+ UF): EUF owns equality + the DT operators.
            atomizer.setDefaultTheory(TheoryId::EUF);
        } else if (logic == "QF_UFDTNIA" || logic == "UFDTNIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::NIA);
            if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
        } else if (logic == "QF_UFDTLIA" || logic == "UFDTLIA") {
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::LIA);
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
        } else if (logic == "QF_ANIA" || logic == "ANIA" ||
                   logic == "QF_AUFNIA" || logic == "AUFNIA") {
            // Arrays + NIA (+ UF): combination atomizer routes array/UF atoms to
            // EUF (which hosts the ArrayReasoner) and pure-arith atoms to NIA.
            // Without this branch the dispatch falls to feature-routing and sets
            // the default theory to LIA, bypassing combination routing — the
            // (= bridge (select ...)) array-read bridges then go to the linear
            // extractor, which cannot parse a Select. Mirrors QF_UFNIA.
            atomizer.setDefaultTheory(TheoryId::Combination);
            atomizer.setSharedTermRegistry(sharedTermRegistry_.get());
            atomizer.setCombinationArithTheory(TheoryId::NIA);
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

        // PG-CNF (XOLVER_PP_PG_CNF): pre-compute the occurrence polarity of every
        // subformula (each assertion is a positive root) so the monotone
        // connectives below emit only the required half of their definition.
        phase("setup-done");
        // Farkas-Or Phase 0 hook: dump pre-atomization structural profile
        // to a file (env XOLVER_NIA_FARKAS_DUMP=1 enables; output goes to
        // XOLVER_NIA_FARKAS_DUMP_FILE or /tmp/farkas_dump). Pure
        // diagnostic — no behavioral change to the solve.
        if (std::getenv("XOLVER_NIA_FARKAS_DUMP")) {
            const char* path = std::getenv("XOLVER_NIA_FARKAS_DUMP_FILE");
            if (!path || !*path) path = "/tmp/farkas_dump";
            FILE* fdump = std::fopen(path, "a");
            if (fdump) {
                farkas::FarkasOrDetector det(*ir);
                auto profile = det.detect();
                std::string s = det.dump(profile);
                std::fwrite(s.data(), 1, s.size(), fdump);
                std::fputc('\n', fdump);
                std::fclose(fdump);
            }
        }
        atomizer.computePolarities(ir->assertions(), *ir);
        for (ExprId assertion : ir->assertions()) {
            SatLit lit = atomizer.atomize(assertion, *ir);
            sat->addClause({lit});
        }
        phase("atomize-done");

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
#ifdef XOLVER_ENABLE_CASESTATS
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

        // Capture boolean VARIABLE values from the SAT assignment WHILE the
        // model is still live (disconnecting the propagator below invalidates
        // CaDiCaL's val()). Theory models survive disconnect because they are
        // captured via the propagator's assignment view, but pure-boolean vars
        // are not theory-tracked. Used by the strict-validation gate.
        std::unordered_map<std::string, std::string> boolVarVals;
        if (result == SatSolver::SolveResult::Sat) {
            // An atom whose expr is a Kind::Variable is a boolean variable in
            // formula position (numeric vars only appear inside theory atoms,
            // whose expr is the relation node). This holds across paths: the
            // pure-bool Variable case AND the QF_UF/combination
            // BoolTermAsFormula case (recorded as an EUF theory atom over the
            // bool var). Its SAT var carries the var's truth, so capture it
            // regardless of the isTheory flag.
            for (const auto& rec : atomizer.atoms()) {
                if (rec.expr >= ir->size()) continue;
                const auto& e = ir->get(rec.expr);
                if (e.kind != Kind::Variable) continue;
                if (!std::holds_alternative<std::string>(e.payload.value)) continue;
                boolVarVals.emplace(std::get<std::string>(e.payload.value),
                                    sat->value(rec.var) ? "true" : "false");
            }
        }

        cadicalBackend->disconnectPropagator();
        propagator.stats().print(std::cerr);

        Result ret = Result::Unknown;
        if (result == SatSolver::SolveResult::Sat) {
            lastModel_ = theoryManager.getModel();
            ret = Result::Sat;
            // Merge the boolean-variable values captured from the live SAT
            // assignment into the model OUTPUT. Pure-boolean variables are not
            // theory-tracked, so without this the model builder defaults them
            // to false even when they were asserted true (e.g. ite_nested_sat:
            // `(assert c1)(assert c2)` printed c1=c2=false). emplace = first
            // wins, so any authoritative theory value is preserved.
            if (!boolVarVals.empty()) {
                if (!lastModel_) lastModel_ = TheorySolver::TheoryModel{};
                for (const auto& [name, val] : boolVarVals) {
                    lastModel_->assignments.emplace(name, val);
                }
            }
            mergeFixedBindings();
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
                    mergeFixedBindings();
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
            //
            // FIRST try the theory's currently held model
            // (theoryManager.getModel()). When a theory stage like NIA
            // Farkas-Or finds and validator-confirms a SAT model but the
            // SAT-CDCL engine times out before its decisions trail aligns
            // with the theory choice, the theory's currentModel_ already
            // points at a valid witness. Validate it against the original
            // assertions; accept on Satisfied. Sound: only ever
            // Unknown -> Sat with a positively-validated model.
            auto theoryCandidate = theoryManager.getModel();
            bool theoryFlipped = false;
            if (theoryCandidate && !theoryCandidate->assignments.empty()) {
                auto saved = std::move(lastModel_);
                lastModel_ = theoryCandidate;
                if (!boolVarVals.empty()) {
                    for (const auto& [name, val] : boolVarVals) {
                        lastModel_->assignments.emplace(name, val);
                    }
                }
                if (modelPositivelyValidates()) {
                    mergeFixedBindings();
                    ret = Result::Sat;
                    theoryFlipped = true;
                } else {
                    lastModel_ = std::move(saved);
                }
            }
            if (!theoryFlipped) {
                CandidateModelSearch cms(*ir, logic);
                auto cmsResult = cms.run();
                if (cmsResult.found) {
                    lastModel_ = cmsResult.model;
                    mergeFixedBindings();
                    ret = Result::Sat;
                } else {
                    if (lastUnknownReason_.empty()) {
                        lastUnknownReason_ = "SAT: solve returned Unknown (propagator abort or timeout)";
                    }
                    ret = Result::Unknown;
                }
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
            mergeFixedBindings();
            if (arrayModelDefinitelyViolates()) {
                lastUnknownReason_ =
                    "array: SAT model violates an original assertion "
                    "(missed array axiom instance) — gated to Unknown (sound)";
                lastModel_.reset();
                ret = Result::Unknown;
            }
        }

        // UF-COMBINATION SAT soundness floor REMOVED (2026-06-02). The bug
        // classes it caught are now closed at the source:
        //   - Wisa "arg arrangement not closed": XOLVER_COMB_UFARG_ARRANGE
        //     (Phase 1+2, default-on) + XOLVER_EUF_PROP (default-on) close
        //     the UF-argument coincidence cases.
        //   - Wisa "DISEQ_WATCH wrong-UNSAT": XOLVER_UF_DISEQ_WATCH (default-on)
        //     after the BuiltinEval level-tag fix produces sound conflicts.
        //   - Wisa "arith bridge vs UF interp mismatch" (xs-05-16): XOLVER_COMB_
        //     MODEL_BASED (default-on) emits a same-arith-value scalar
        //     arrangement split so EUF merges value-equal bridges with their
        //     constant siblings, eliminating the model-construction skew.
        // Verified: Wisa(30/50) FLOOR OFF + all promoted flags → 0 unsound.
        // unit 1098/1098, regression 670/670. Removing the floor also recovers
        // the small number of genuine sats it over-floored historically.
        // Escape: XOLVER_COMB_VALIDATE_SAT=1 to opt back in if needed.
        if (ret == Result::Sat) {
            const char* e = std::getenv("XOLVER_COMB_VALIDATE_SAT");
            bool optInFloor = e && !(e[0] == '0' && e[1] == '\0');
            auto isCombUfLogic = [](const std::string& L) {
                return L == "QF_UFLIA" || L == "UFLIA" ||
                       L == "QF_UFLRA" || L == "UFLRA";
            };
            if (optInFloor && features.hasUF && !features.hasArray &&
                isCombUfLogic(logic)) {
                if (!lastModel_) lastModel_ = theoryManager.getModel();
                mergeFixedBindings();
                if (combinationModelDefinitelyViolates()) {
                    lastUnknownReason_ =
                        "uf-comb: SAT model violates an original assertion "
                        "(opt-in floor via XOLVER_COMB_VALIDATE_SAT=1)";
                    lastModel_.reset();
                    ret = Result::Unknown;
                }
            }
        }

        // NOTE: datatype sat soundness is enforced precisely inside the theory
        // layer (EufSolver::satComplete blocks a sat unless every datatype
        // e-class has a determined constructor — a concrete ground-term model).
        // No blanket DT-sat floor here: a fully-determined consistent DT model
        // is a sound sat; only constructor-undetermined cases fall through to
        // Unknown via satComplete.

        // STRICT model-validation gate (XOLVER_PP_STRICT_VALIDATION, default
        // OFF). The systemic soundness backstop: only emit `sat` when the
        // extracted model is POSITIVELY confirmed against the original
        // assertions. The default path downgrades only on a DEFINITE Violated,
        // so a model the validator cannot fully evaluate (Indeterminate —
        // uninterpreted function, missing/unsupported construct, incomplete
        // extraction) escapes as an unvalidated sat. Under strict mode that is
        // downgraded to `unknown` ("never trust an unconfirmed model").
        //
        // Soundness: this ONLY ever turns sat -> unknown; it never produces a
        // sat or flips unsat, so it cannot introduce a wrong answer. It is
        // EXPECTED to convert some genuine sats to unknown until model
        // extraction (theory agents) lets the validator confirm them; that
        // completeness loss is the documented trade for closing the false-sat
        // class, and promotion to default-on waits on that work.
        // Scoped variant (XOLVER_PP_VALIDATE_NONLINEAR_SAT): enforce invariant 1
        // (a Result::Sat must be ModelValidator-backed) specifically for the
        // INCOMPLETE nonlinear theories (NIA/NRA/NIRA — features.hasNonlinear).
        // Those return "no conflict found" = sat without a validated model, so
        // an actually-unsat nonlinear system can escape as a false-SAT whose
        // candidate violates an asserted (dis)equality (e.g. the AProVE NIA
        // class: all-zero satisfies the inequalities but violates a nonlinear
        // disequality). Validating the model (and CMS-recovering it) downgrades
        // such an unconfirmable sat to `unknown`. Narrower than the global
        // strict gate (leaves complete logics' sat untouched), so it is closer
        // to promotable for QF_NIA/NRA/NIRA once the theory recovery lands.
        // NIA (nonlinear INTEGER, no real vars) validate-sat is DEFAULT-ON: it
        // enforces invariant 1 for an incomplete theory, and measurement shows
        // it loses ZERO genuine NIA sats (integer models validate exactly) while
        // flooring the false-SAT class to `unknown` — a strict wrong->unknown
        // win with no regression on correct answers. NRA/NIRA stay behind the
        // opt-in flag: their algebraic real witnesses are not yet evaluable by
        // the (rational) validator, so default-on there would flip ~14 genuine
        // sats to unknown (recovered separately via algebraic validation).
        bool niaSatFloor = features.hasNonlinear && !features.hasRealVar;
        // Div/mod-by-constant is LINEAR (hasNonlinear=false), so it slips past
        // the nonlinear floor above -- yet the div/mod lowering can yield a
        // spurious sat whose model satisfies the lowered linear-mod system but
        // not the original mod relations (e.g. SVCOMP soft_float: many
        // (mod m 2^k) clauses; xolver=sat, oracle=unsat). Validate the sat for
        // such (pure-Int) div/mod-lowered formulas too. Sound: only sat->unknown.
        // Exclude UF: div/mod-by-zero under UF is a partial function the
        // validator cannot positively confirm (genuine UFNIA divzero sats would
        // be over-floored to unknown); leave those to UF-aware validation.
        bool divModSatFloor = !divModOrigins_.empty() &&
                              !features.hasRealVar && !features.hasUF;
        // Real-division purification (promoted default-ON) introduces fresh `q`
        // for real `(/ a b)` with the guarded def `b!=0 => q*b=a`. For b!=0 this
        // pins q=a/b exactly; for b==0 q is left free (SMT-LIB div-by-0 is
        // unconstrained). The only residual soundness gap is the div-by-0
        // functional-consistency corner (distinct (/ a 0),(/ a' 0) with a=a'
        // could diverge here). Co-activate the nonlinear-real SAT floor so every
        // such sat is re-validated against the ORIGINAL `(/ a b)`: the validator
        // computes a/b for b!=0 (confirms genuine sats) and returns Indeterminate
        // for b==0 (downgrades the corner to unknown via CMS re-validation).
        // Invariant 1 + corner soundness.
        bool realDivPurifySatFloor = features.hasNonlinear && features.hasRealVar;
        // Array-combination SAT floor (QF_ALIA/ALRA/AUFLIA/AUFLRA). In these
        // Nelson-Oppen logics the arrangement between the array/EUF e-graph and
        // the arith solver can declare a model "consistent" at the Full-effort
        // check while a conflict found mid-search has ESCAPED (the read2
        // conflict-stickiness class) — yielding a false-SAT (xolver=sat,
        // z3=unsat). The definite-Violated array floor (arrayModelDefinitelyViolates)
        // misses it because the combined model is only INDETERMINATE to the
        // validator (incomplete cross-theory extraction), not a definite
        // violation. Enforce invariant 1: a Result::Sat must be
        // ModelValidator-backed -> require POSITIVE validation of the combined
        // (array+arith) model; an unconfirmable array-combination sat downgrades
        // to unknown (with CMS recovery first). Sound: only ever sat->unknown,
        // never a wrong verdict. Eliminates the read2 false-SAT (verified).
        // DEFAULT-OFF (XOLVER_ARRAY_COMB_VALIDATE_SAT): promotion to default-ON is
        // GATED on combination model-recovery — CandidateModelSearch has no array
        // support, so it cannot rebuild a positively-validatable model for genuine
        // array-combination sats whose scalars/array-interps the theory left
        // incomplete (e.g. alia_005 asserts i!=j but the model defaults i=j=0 ->
        // spurious violation; alra_010 nested-row2). Default-ON today regresses
        // those 2 genuine sats to unknown (suite 661->659). Promote once #12
        // (N-O valid model construction: distinct asserted-diseq scalars + array
        // interps for declared arrays) lets them validate positively. Pure QF_AX
        // is excluded (opaque sorts -> definite-Violated floor already guards it).
        auto isCombArrayLogic = [](const std::string& L) {
            return L == "QF_ALIA" || L == "ALIA" || L == "QF_ALRA" || L == "ALRA" ||
                   L == "QF_AUFLIA" || L == "AUFLIA" || L == "QF_AUFLRA" || L == "AUFLRA";
        };
        bool arrayCombSatFloor = features.hasArray && isCombArrayLogic(logic) &&
                                 std::getenv("XOLVER_ARRAY_COMB_VALIDATE_SAT") != nullptr;
        bool validateSat = niaSatFloor || divModSatFloor || realDivPurifySatFloor ||
                           arrayCombSatFloor ||
                           (std::getenv("XOLVER_PP_STRICT_VALIDATION") != nullptr) ||
                           (features.hasNonlinear &&
                            std::getenv("XOLVER_PP_VALIDATE_NONLINEAR_SAT") != nullptr);
        if (ret == Result::Sat && validateSat) {
            if (!lastModel_) lastModel_ = theoryManager.getModel();
            // Theory models do not track pure-boolean VARIABLES (those values
            // live in the SAT assignment). Populate them from the SAT solver so
            // the validator checks the same model that would be printed and only
            // flips genuinely-unconfirmable cases (uninterpreted functions,
            // incomplete theory extraction) rather than every bool-containing
            // sat. A first-wins emplace keeps any authoritative theory value.
            if (!lastModel_) lastModel_ = TheorySolver::TheoryModel{};
            // Merge the boolean-variable values captured from the live SAT model
            // (theory models do not track pure-boolean vars). emplace = first
            // wins, so an authoritative theory value is preserved.
            for (const auto& [name, val] : boolVarVals) {
                lastModel_->assignments.emplace(name, val);
            }
            mergeFixedBindings();
            if (!modelPositivelyValidates()) {
                // RECOVERY (unknown -> correct sat): the theory's extracted
                // model could not be positively confirmed, but the verdict is
                // sat, so a satisfying model exists. Search for a complete one
                // (CandidateModelSearch builds full numeric models AND function
                // interps), then INDEPENDENTLY re-validate it. We keep sat only
                // if the independent validator now confirms Satisfied — so this
                // recovers genuine sats without ever trusting an unconfirmed
                // model. Cases the search/validator still cannot confirm
                // (uninterpreted-sort UF, algebraic NRA witnesses, …) remain
                // the genuinely-hard residual and stay unknown.
                auto saved = std::move(lastModel_);
                CandidateModelSearch::Config cfg;
                cfg.assertionRootsOverride = originalAssertions_;
                cfg.allowUF = true;
                CandidateModelSearch cms(*ir, logic, cfg);
                auto rec = cms.run();
                bool recovered = false;
                if (rec.found) {
                    lastModel_ = rec.model;
                    for (const auto& [name, val] : boolVarVals) {
                        lastModel_->assignments.emplace(name, val);
                    }
                    mergeFixedBindings();
                    recovered = modelPositivelyValidates();
                }
                if (!recovered) {
                    lastModel_ = std::move(saved);
                    lastUnknownReason_ =
                        "strict-validation: model not positively confirmed "
                        "(Indeterminate) — gated to Unknown (sound)";
                    lastModel_.reset();
                    ret = Result::Unknown;
                }
            }
        }

        // Replay solve-eqs eliminations onto the final model so it satisfies
        // the ORIGINAL assertions (which still reference the eliminated vars).
        // If any eliminated var cannot be reconstructed, we cannot vouch for
        // the model: downgrade Sat -> Unknown (sound floor) rather than emit
        // an unvalidatable model (invariant 1).
        //
        // Materialize an empty lastModel_ when SAT and the converter has work
        // to do but no theory built a model. This happens when SolveEqs has
        // eliminated every variable, so the residual formula is trivially
        // true and the theory layer returns SAT-with-empty-model. Without
        // this, modelConverter_.reconstruct is skipped, and tests like
        // `(= x 42)` see an empty model after the elimination instead of
        // the replayed x=42. The reconstruct still validates over the
        // ORIGINAL assertions internally; sound either way.
        if (ret == Result::Sat && !modelConverter_.empty() && !lastModel_) {
            lastModel_ = TheorySolver::TheoryModel{};
        }
        if (ret == Result::Sat && lastModel_ && !modelConverter_.empty()) {
            if (!modelConverter_.reconstruct(lastModel_->numericAssignments,
                                             lastModel_->assignments, *ir)) {
                lastUnknownReason_ = "solve-eqs: eliminated variable not reconstructable";
                lastModel_.reset();
                ret = Result::Unknown;
            }
        }

#ifdef XOLVER_ENABLE_CASESTATS
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
    // Pre-register the standard sorts so the IR sees a non-NullSort
    // boolSortId/intSortId/realSortId before any user assertion or
    // checkSat() call. Without this, an API-mode user that never calls
    // boolSort()/intSort() explicitly leaves the IR's sort table empty,
    // which downstream (BoolSubtermPurifier, Atomizer, model dump) treat
    // as "Boolean variables not classifiable" — producing empty models
    // and broken get-model behavior. CLI gets these sorts populated as
    // a side effect of SOMTParser; the API never had that bridge.
    // Sound because allocating a sort id is idempotent (getOrCreateXxx
    // returns the cached id on repeat calls).
    pImpl->getOrCreateBoolSort();
    if (logic.find("LIA") != std::string_view::npos ||
        logic.find("NIA") != std::string_view::npos ||
        logic.find("LIRA") != std::string_view::npos ||
        logic.find("NIRA") != std::string_view::npos ||
        logic.find("IDL") != std::string_view::npos ||
        logic.find("DTLIA") != std::string_view::npos ||
        logic.find("DTNIA") != std::string_view::npos ||
        logic.find("ALIA") != std::string_view::npos ||
        logic.find("ANIA") != std::string_view::npos) {
        pImpl->getOrCreateIntSort();
    }
    if (logic.find("LRA") != std::string_view::npos ||
        logic.find("NRA") != std::string_view::npos ||
        logic.find("LIRA") != std::string_view::npos ||
        logic.find("NIRA") != std::string_view::npos ||
        logic.find("RDL") != std::string_view::npos ||
        logic.find("ALRA") != std::string_view::npos) {
        pImpl->getOrCreateRealSort();
    }
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
    // A programmatic assertion would be lost on a portfolio re-parse, so it
    // taints re-parseability: the portfolio executor must stay single-arm.
    pImpl->sourcePath_.clear();
}

Result Solver::checkSat() {
    // Start the global solve wall-clock so per-engine budgets can scale to the
    // time remaining (P0-A). Unset / 0 => no deadline => no behavior change.
    wall::beginSolve(env::paramLong("XOLVER_WALLCLOCK_MS", 0));
    Result r;
    // Top-level bad_alloc firewall (iter#18, pre-existing class). A pathological
    // input (e.g. AProVE aproveSMT4461031801876451415: 16 vars + nested
    // assertion) can OOM deep in atomization / theory / SAT layers before any
    // budget-guard reacts. Returning Unknown via this catch is sound and
    // preserves the solver process (vs aborting with std::terminate or
    // emitting the `(error std::bad_alloc)` token that downstream pipelines
    // interpret as a hard crash). The catch is at the OUTER boundary so any
    // bad_alloc — regardless of which inner stage allocated past the
    // process limit — surfaces as a clean Unknown verdict.
    try {
        r = std::getenv("XOLVER_STRAT_PORTFOLIO")
                ? pImpl->checkSatPortfolio()
                : pImpl->checkSatInternal();
    } catch (const std::bad_alloc&) {
        pImpl->lastUnknownReason_ = "out-of-memory (bad_alloc) — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    } catch (const std::length_error& e) {
        // libgmp / std::vector etc. throw length_error when a polynomial DAG
        // attempts to construct a container past max_size — a different
        // exception class than bad_alloc but the same crash-class symptom.
        // Iter#19 extension of the iter#18 firewall: same Unknown-conversion
        // contract.
        pImpl->lastUnknownReason_ =
            std::string("length_error (") + e.what() +
            ") — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    } catch (const std::exception& e) {
        // Catch-all for any other std::exception escaping the inner solve.
        // Sound: returns Unknown for any case the solver could not complete
        // cleanly. Preserves the solver process for downstream cases (e.g.
        // run_regression --j-mode running many files per worker).
        pImpl->lastUnknownReason_ =
            std::string("exception (") + e.what() +
            ") — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    }
    wall::endSolve();
    return r;
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

    // Map variable names to ExprIds from CoreIr. Prefer the string
    // `assignments` channel; fall back to the typed `numericAssignments`
    // channel (RealValue) when the string channel is empty. The numeric
    // channel is the path the LIA solver uses by default when no string
    // serialization is requested. Without this fallback, an API-mode
    // caller (Solver::getModel() invoked programmatically, no CLI
    // `get-model` command) sees an empty Model even on a successful
    // checkSat → Sat. Pre-existing bug uncovered by test_api LIA test.
    if (pImpl->ir) {
        for (ExprId id = 0; id < static_cast<ExprId>(pImpl->ir->size()); ++id) {
            const auto& expr = pImpl->ir->get(id);
            if (expr.kind != Kind::Variable) continue;
            if (!std::holds_alternative<std::string>(expr.payload.value)) continue;
            const std::string& name = std::get<std::string>(expr.payload.value);
            auto it = theoryModel.assignments.find(name);
            if (it != theoryModel.assignments.end()) {
                model.setValue(id, it->second);
                continue;
            }
            // Fallback: typed numeric channel.
            auto nit = theoryModel.numericAssignments.find(name);
            if (nit != theoryModel.numericAssignments.end()) {
                if (auto q = nit->second.tryAsRational()) {
                    model.setValue(id, q->get_str());
                }
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

#ifdef XOLVER_ENABLE_CASESTATS
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

} // namespace xolver
