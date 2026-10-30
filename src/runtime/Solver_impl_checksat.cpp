#include "base/RuntimeConfig.h"
#include "base/EnvParam.h"
#include "runtime/SolverImpl.h"
#include "ir/NativeFeatures.h"
#include "applications/satisfiability/smt/Solver.h"
#include "applications/verification/sl/Solver.h"
#include "search/array/ArrayModelCompletion.h"
#include "search/linear/BoundAxiomGenerator.h"
#include "search/refute/PolynomialBooleanRefutation.h"

namespace xolver {
// Relocated Solver::Impl method definitions (declared in SolverImpl.h).

Result Solver::Impl::checkSatInternal() {
        lastUnknownReason_.clear();
        lastUnknownCode_.clear();
        lastUnknownComponent_.clear();
        lastUnknownDetail_.clear();
        lastModel_.reset();
        divModOrigins_.clear();
        partialFuncModel_ = PartialFuncModel{};
        roaeReads_.clear();
        originalAssertions_.clear();
        if (parser && parser->getHeapLocationSort()) {
            // declare-heap explicitly selects SL semantics in SMT-LIB. Arrays
            // or symbols named heap/pointer alone never enter this application.
            auto& terms = ensureIr();
            originalAssertions_ = terms.assertions();
            originalAssertions_.insert(originalAssertions_.end(),
                                       assumptionRoots_.begin(), assumptionRoots_.end());
            std::vector<SOMTParser::Node> roots;
            for (auto id : originalAssertions_) roots.push_back(terms.native(id));
            sl::Request request;
            request.location = parser->getHeapLocationSort();
            request.data = parser->getHeapDataSort();
            request.assertions = std::move(roots);
            request.declarations = parser->getDeclaredVariables();
            const auto& declaredLogic = parser->getOptions()->logic;
            if (declaredLogic == "QF_SHID" || declaredLogic == "SHID" ||
                declaredLogic == "QF_SHIDLIA" || declaredLogic == "SHIDLIA" ||
                declaredLogic == "QF_SHLID" || declaredLogic == "QF_SHLS")
                request.recursion = sl::RecursiveSemantics::LeastFixedPoint;
            for (const auto& definition : parser->getRecursiveDefinitions())
                request.definitions.push_back({definition.symbol, definition.definition->getFuncBody(),
                                               definition.definition->getFuncParams()});
            auto decision = sl::solve(request);
            lastUnknownReason_ = std::move(decision.reason);
            lastModel_ = std::move(decision.model);
            if (decision.result == Result::Unsat && assumptionRoots_.empty()) {
                lastUnsatCore_.clear();
                for (auto root : originalAssertions_) lastUnsatCore_.emplace_back(root, contextId_);
            }
            return decision.result;
        }
        const auto traceOption = options.find("produce-pa-certificate");
        const bool recordPA = traceOption != options.end() &&
            traceOption->second.kind == OptionValue::Bool && traceOption->second.b;
        if (!ir && !recordPA) return Result::Sat;
        if (!ir) ensureIr();
        if (ir->assertions().empty() && assumptionRoots_.empty() && !recordPA) {
            lastModel_ = TheorySolver::TheoryModel{};
            return Result::Sat;
        }

        struct AssertionRestore {
            NativeTerms& ir;
            std::vector<std::pair<ScopeLevel, ExprId>> saved;
            ~AssertionRestore() { ir.restoreAssertions(std::move(saved)); }
        } restore{*ir, ir->getScopedAssertions()};

        // Snapshot the ORIGINAL (pre-lowering) assertion roots for the
        // independent model self-check (modelMatchesOriginal). Lowering
        // passes only APPEND TermExpr nodes (NativeTerms::add never mutates), so
        // these ExprIds keep referencing the original formula even after
        // the assertion list is rewritten by lowering.
        originalAssertions_ = ir->assertions();

        // First-order formulas must be handled before any ground
        // rewriting, substitution or SAT abstraction can cross a binder.
        auto quantifiedRoots = originalAssertions_;
        quantifiedRoots.insert(quantifiedRoots.end(), assumptionRoots_.begin(), assumptionRoots_.end());
        const auto nativeRoots = ir->native(quantifiedRoots);
        applications::satisfiability::smt::Problem problem{nativeRoots, {}, {.elimination = recordPA}};
        const auto features = nativeFeatures(nativeRoots);
        if (recordPA || (features.quantified && features.integer && !features.real && !features.bitvector)) {
            const long work = config::read<config::ReadKind::Long>("XOLVER_PA_WORK", 2000000);
            const long residues = config::read<config::ReadKind::Long>("XOLVER_PA_RESIDUES", 100000);
            if (work >= 0) problem.integerLimits.work = static_cast<size_t>(work);
            if (residues >= 0) problem.integerLimits.residues = static_cast<size_t>(residues);
        }
        bool usedGround = false;
        applications::satisfiability::smt::Solver application([&](const applications::satisfiability::smt::Problem&) {
            usedGround = true;
            SolverAnswer answer;
            answer.result = checkSatGround();
            answer.reason = std::move(lastUnknownReason_);
            answer.model = std::move(lastModel_);
            answer.proof = std::move(lastProof_);
            return answer;
        });
        auto answer = application.solve(problem);
        lastUnknownReason_ = std::move(answer.reason);
        lastModel_ = std::move(answer.model);
        lastProof_ = std::move(answer.proof);
        if (!usedGround) {
            originalAssertions_ = quantifiedRoots;
            // A full-assertion core is conservative until the logical backend
            // supplies a smaller core. Assumptions have their own core API.
            if (answer.result == Result::Unsat && assumptionRoots_.empty()) {
                lastUnsatCore_.clear();
                for (auto root : originalAssertions_) lastUnsatCore_.emplace_back(root, contextId_);
            }
        }
        return answer.result;
}

Result Solver::Impl::checkSatGround() {
        struct QueryLogicRestore {
            std::string& logic;
            std::string declared;
            ~QueryLogicRestore() { logic = std::move(declared); }
        } restoreLogic{logic, logic};
        // Lowering can introduce an arithmetic sort absent from the input:
        // e.g. (is_int r) creates an Int witness in an otherwise Real DAG.
        getOrCreateBoolSort();
        getOrCreateIntSort();
        getOrCreateRealSort();

        // Assumptions must participate in feature detection and lowering, and
        // in every candidate-model check. Guard them with fresh indicators so
        // CaDiCaL can still minimize the assumption core after preprocessing.
        std::vector<ExprId> assumptionIndicators;
        for (ExprId root : assumptionRoots_) {
            originalAssertions_.push_back(root);
            ExprId indicator = ir->makeFreshVariable(getOrCreateBoolSort(), "__xolver_assume", true);
            ir->addAssertion(ir->add(TermExpr{Kind::Implies, ir->boolSortId(),
                                             {indicator, root}, Payload{}}));
            assumptionIndicators.push_back(indicator);
        }

        // File-level unsat-core gating (:produce-unsat-cores). Replace each
        // top-level assertion A with (=> a A) for a fresh indicator a, BEFORE
        // lowering, so the CNF guard distributes into every clause derived from A
        // (AND-flatten/rewrite preserve the implication). All indicators are
        // assumed in the solve below; failed() then reports which ORIGINAL
        // assertions (indicatorCoreTerms_) form the core. Gated → the default path
        // is byte-identical. originalAssertions_ keeps the UNGUARDED roots for the
        // model self-check. (Re-entrant solves — portfolio/escalating — would
        // re-guard; produce-unsat-cores is a single-solve CLI/API mode.)
        produceUnsatCores_ = parser && parser->getOptions() &&
                             parser->getOptions()->get_unsat_core;
        if (auto itUc = options.find("produce-unsat-cores");
            itUc != options.end() && itUc->second.kind == OptionValue::Bool &&
            itUc->second.b)
            produceUnsatCores_ = true;
        indicatorRoots_.clear();
        indicatorCoreTerms_.clear();
        {
            SortId bsid = (boolSortId_ != NullSort) ? boolSortId_ : ir->boolSortId();
            if (produceUnsatCores_ && bsid != NullSort) {
                const std::vector<std::pair<ScopeLevel, ExprId>> scoped =
                    ir->getScopedAssertions();
                ir->clearAssertions();
                for (const auto& [lv, eid] : scoped) {
                    ExprId a = ir->makeFreshVariable(bsid, "__xolver_uc", true);
                    ExprId guarded =
                        ir->add(TermExpr{Kind::Implies, bsid, {a, eid}, Payload{}});
                    ir->addAssertion(guarded, lv);
                    indicatorRoots_.push_back(a);
                    indicatorCoreTerms_.push_back(Term(eid, contextId_));
                }
                // Conservative fallback core (used only if UNSAT is proven before
                // the SAT solve, so failed() never runs): the full assertion set.
                lastUnsatCore_ = indicatorCoreTerms_;
            }
        }

        // Coarse phase timing (SOLVE_PHASE_PROF) to localize a pre-solve hang.
        // Uses C-level stderr (fprintf), NOT std::cerr: checkSatInternal can run
        // on a worker thread whose std::cerr is redirected/suppressed, which
        // silently swallowed every [PHASE] line and made the profiler useless.
        const bool phaseProf = xolver::config::read<xolver::config::ReadKind::Presence>("SOLVE_PHASE_PROF");
        auto phaseClock = std::chrono::steady_clock::now();
        auto phase = [&](const char* nm) {
            if (!phaseProf) return;
            auto now = std::chrono::steady_clock::now();
            std::fprintf(stderr, "[PHASE] %s  +%lldms (asserts=%zu)\n", nm,
                         static_cast<long long>(
                             std::chrono::duration_cast<std::chrono::milliseconds>(
                                 now - phaseClock).count()),
                         ir->assertions().size());
            std::fflush(stderr);
            phaseClock = now;
        };
        phase("enter");

        // Preserve read-only array shapes until targeted elimination runs.
        const bool enableRewrite = !(logic == "QF_ANIA" || logic == "QF_AUFNIA" ||
                                     logic == "ANIA" || logic == "AUFNIA");
        auto rewriteAssertions = [&]() {
            if (!enableRewrite) return false;
            FormulaRewriter rewriter(*ir, boolSortId_);
            if (rewriter.run() == FormulaRewriter::Verdict::Unsat) {
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unsat, 0.0);
#endif
                return true;
            }
            rewriter.commit();
            return false;
        };
        if (rewriteAssertions()) return Result::Unsat;
        phase("rewrite-done");

        // Eliminate reconstructable definitions at base scope.
        modelConverter_ = ModelConverter{};
        fixedBindings_.clear();
        const bool differenceLogic = logic == "QF_IDL" || logic == "IDL" ||
                                     logic == "QF_RDL" || logic == "RDL";
        if (ir->currentScopeLevel() == 0 && !differenceLogic) {
            const bool polynomialDefinitions = logic == "QF_NIA";
            const auto policy = polynomialDefinitions
                ? SolveEqs::DefinitionPolicy::PolynomialInLinearPositions
                : SolveEqs::DefinitionPolicy::PolynomialReals;
            SolveEqs solveEqs(*ir, modelConverter_, policy);
            // A committed substitution and its replay steps form a transaction.
            // Keep earlier committed progress if a later pass exhausts memory.
            // The same SolveEqs object retains the total substitution-work cap.
            for (;;) {
                try {
                    auto savedConverter = modelConverter_;
                    try {
                        if (!solveEqs.run()) break;
                        solveEqs.commit();
                    } catch (const std::bad_alloc&) {
                        modelConverter_ = std::move(savedConverter);
                        throw;
                    }
                    std::cerr << "[SolveEqs] eliminated " << solveEqs.eliminatedCount()
                              << " variable(s)\n";
                    if (!polynomialDefinitions || !enableRewrite) break;
                    if (rewriteAssertions()) return Result::Unsat;
                } catch (const std::bad_alloc&) {
                    std::cerr << "[SolveEqs] memory exhausted; keeping committed simplifications\n";
                    break;
                }
            }
        }

        // Reset SAT solver for fresh query.
        phase("solve-eqs-done");
        sat = createSatSolver();

#ifdef XOLVER_ENABLE_PROOFS
        // UNSAT proof tracing (opt-in via --produce-proofs / setOption). Must be
        // enabled here — right after the fresh solver, before atomization feeds
        // any clause (CaDiCaL CONFIGURING state). If the backend declines (e.g.
        // not built with proof support) we proceed in degraded no-proof mode: an
        // unsat is still emitted, just without a certificate. Never a wrong proof.
        {
            auto pit = options.find("produce-proofs");
            if (pit != options.end() &&
                pit->second.kind == OptionValue::String && !pit->second.s.empty()) {
                sat->enableProofTrace(pit->second.s, /*lrat=*/false);
                // Install the per-solve theory-certificate sink so theory solvers
                // can push Alethe justifications (Phase C); the backend's proof
                // finalizer drains it. Re-cleared each query.
                proofSink_.clear();
                proof::setActiveProofSink(&proofSink_);
            } else {
                proof::setActiveProofSink(nullptr);
            }
        }
#endif

        // Symbolic-modular simplification of `(mod p M)` for non-constant M
        // (the bit-width-independent Zohar `pow2(k)` modulus) must run BEFORE
        // ITE lowering: it pushes a mod through the `intmodtotal` ite-wrapper
        // (`(mod (ite C a b) M) -> (ite C (mod a M)(mod b M))`) and drops
        // M-divisible monomials, which only works while the ites are still ites.
        // Once IteLowerer replaces them with fresh vars the structure is
        // opaque to the rewrite. Sound, general; no-op unless a non-constant
        // modulus is present. (The same pass runs again after lowering for
        // constant div/mod folding.)
        {
            IntDivModConstantFold preMod(*ir);
            preMod.run();
            preMod.commit();
            if (preMod.didFold() && rewriteAssertions()) return Result::Unsat;
        }
        phase("symbolic-mod-done");

        // Lower ITEs before any theory processing or atomization.
        // IteLowerer is a pure IR-to-IR pass: no SatLit, no theory atom
        // registration, no SAT clause insertion.
        {
            IteLowerer lowerer(*ir);
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
        phase("ite-lowering-done");
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
        phase("constant-propagation-done");

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

        // Eliminate read-only arrays only when the fragment check succeeds.
        {
            ReadOnlyArrayElim roae(*ir);
            if (roae.run()) {
                roae.commit();
                roaeReads_ = roae.reads();
            }
        }

        // uninterpreted-function applications (QF_UFNRA "hidden nonlinearity"
        // FFT family). Exact reduction; the UNSAT direction needs no model
        // reconstruction (a SAT over the abstracted formula floors to Unknown).
        // Restricted to QF_UFNRA: it is net-positive there (the nonlinear term
        // hides in a UF arg) but net-NEGATIVE on QF_UFNIA (0 flips, regresses
        // solved cases by abstracting UF the combination was using).
        if (logic == "QF_UFNRA" || logic == "UFNRA") {
            UfApplyAckermann ufack(*ir);
            if (ufack.run()) ufack.commit();
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
            if (dmFold.didFold() && rewriteAssertions()) return Result::Unsat;
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
            // which is default-ON (2026-06-04 overnight iter #4): without EUF
            // available, int div/mod-by-variable in QF_ANIA bailed to unknown
            // (SVCOMP UltimateAutomizer family). Opt-out via
            bool arrayNiaRoutedEuf =
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
                // Div/mod at zero are total, congruent functions even in an
                // arithmetic-only input logic. Select the existing combination
                // stack for the generated functions, scoped to this query.
                if (logic == "QF_NIA" || logic == "NIA")
                    logic = "QF_UFNIA";
                else if (logic == "QF_LIA" || logic == "LIA" ||
                         logic == "QF_IDL" || logic == "IDL")
                    logic = "QF_UFLIA";
                else if (logic != "ALL") {
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
        }
        // Lowering exposes bindings for the fresh quotient/remainder symbols.
        // Propagate them before feature detection so e.g. d*q with q=5 is
        // handled as linear arithmetic, including the guarded zero branch.
        if (!divModOrigins_.empty()) {
            UnconditionalConstantPropagation constants(*ir);
            constants.run();
            if (constants.hadContradiction()) return Result::Unsat;
            for (const auto& [name, value] : constants.fixedConstMap())
                fixedBindings_.insert_or_assign(name, value);
            constants.commit();
        }
        phase("integer-divmod-done");

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

        // Fresh per-check-sat instances
        TheoryAtomRegistry registry;
        TheoryManager theoryManager;
        TheoryLemmaDatabase lemmaDb;
        PolynomialKernel* polyKernelRaw = nullptr;

        // Detect features from NativeTerms for safe routing
        LogicFeatureDetector detector(*ir);
        LogicFeatures features = detector.detect();
        // ALL must select the same UF/arithmetic combination for both the
        // theory factory and the atomizer. Arithmetic-only feature routing
        // cannot handle the equalities linking a UF application to its value.
        if (logic == "ALL" && features.hasUF && !features.hasArray && !features.hasDatatype) {
            const auto domain = nativeFeatures(ir->native(originalAssertions_));
            if (domain.integerValue && domain.realValue) {
                lastUnknownReason_ = "automatic UF/mixed-arithmetic combination is unavailable";
                return Result::Unknown;
            }
            const auto arithmetic = domain.realValue
                ? (features.hasNonlinear ? TheoryId::NRA : TheoryId::LRA)
                : domain.integerValue ? (features.hasNonlinear ? TheoryId::NIA : TheoryId::LIA)
                                      : featureArithmeticTheory(features);
            switch (arithmetic) {
            case TheoryId::Bool: logic = "QF_UF"; break;
            case TheoryId::LIA: logic = "QF_UFLIA"; break;
            case TheoryId::LRA: logic = "QF_UFLRA"; break;
            case TheoryId::NIA: logic = "QF_UFNIA"; break;
            case TheoryId::NRA: logic = "QF_UFNRA"; break;
            default:
                lastUnknownReason_ = "automatic UF/mixed-arithmetic combination is unavailable";
                return Result::Unknown;
            }
        }
        phase("detect-done");
        if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_DUMP_FINAL_ASSERTS")) {
            int di = 0;
            for (ExprId aid : ir->assertions())
                std::fprintf(stderr, "[FINAL-ASSERT %d] %s\n", di++,
                             dumpExprToSMT2(aid, *ir).c_str());
            std::fflush(stderr);
        }

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
        {
            if (!features.hasArray && !features.hasUF) {
                std::string dg;
                if (logic == "QF_AUFLIA" || logic == "AUFLIA" ||
                    logic == "QF_ALIA" || logic == "ALIA") dg = "QF_LIA";
                else if (logic == "QF_AUFLRA" || logic == "AUFLRA" ||
                         logic == "QF_ALRA" || logic == "ALRA") dg = "QF_LRA";
                if (!dg.empty()) {
                    if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_ARRAY_NOARR_DOWNGRADE_DIAG"))
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
        // answer, not an unsound one.
        {
            if (!features.hasNonlinear &&
                (logic == "QF_NRA" || logic == "NRA")) {
                if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_LINEAR_DOWNGRADE_DIAG"))
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
        // never SAT/UNSAT.
        {
            if (!features.hasNonlinear &&
                (logic == "QF_NIA" || logic == "NIA" ||
                 logic == "QF_UFNIA" || logic == "UFNIA")) {
                if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_LINEAR_DOWNGRADE_DIAG"))
                    std::cerr << "[NIA-LINEAR-DOWNGRADE] " << logic
                              << " -> QF_LIA (no nonlinear terms)\n";
                logic = features.hasUF ? "QF_UFLIA" : "QF_LIA";
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
        // additionally admits the array+nonlinear-integer logics
        // QF_ANIA/QF_AUFNIA: arrays layered on the EUF e-graph with a purified
        // NIA core underneath (see TheoryFactory). SAT results still pass the
        // nonlinear validate-sat floor (unconfirmed → unknown). Opt-out via
        auto isArrayLogic = [&](const std::string& l) {
            bool base = l == "QF_AX" ||
                   l == "QF_ALIA" || l == "ALIA" ||
                   l == "QF_ALRA" || l == "ALRA" ||
                   l == "QF_AUFLIA" || l == "AUFLIA" ||
                   l == "QF_AUFLRA" || l == "AUFLRA";
            bool arrayNia =
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

        // Give exact, explained Boolean/theory refutation a bounded attempt
        // before a SAT-only portfolio arm. The polynomial rules are shared by
        // integer and real arithmetic; an open relaxation changes no verdict.
        if (features.hasNonlinear && !features.hasUF && !features.hasArray &&
            !features.hasDatatype && !features.hasUnsupported) {
            auto roots = ir->assertions();
            roots.insert(roots.end(), assumptionIndicators.begin(), assumptionIndicators.end());
            roots.insert(roots.end(), indicatorRoots_.begin(), indicatorRoots_.end());
            const auto started = std::chrono::steady_clock::now();
            BooleanRefutationLimits limits;
            limits.deadline = started + std::chrono::milliseconds(50);
            PolynomialBooleanStatistics stats;
            const bool refuted = refutePolynomialBoolean(*ir, roots, limits, &stats);
            const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
            if (!profile.empty()) {
                std::ofstream out(profile.string() + ".boolean-refutation.log", std::ios::app);
                out << "atoms=" << stats.convertedAtoms << " assignments=" << stats.boolean.assignments
                    << " conflicts=" << stats.boolean.conflicts << " theory_calls=" << stats.theoryCalls
                    << " largest_context=" << stats.largestContext << " theory_us=" << stats.theoryMicroseconds
                    << " sign_exhaustions=" << stats.signExhaustions
                    << " linear_calls=" << stats.linearCalls << " linear_rows=" << stats.linearConstraints
                    << " linear_exhaustions=" << stats.linearExhaustions << " linear_us=" << stats.linearMicroseconds
                    << " exhausted=" << stats.exhausted << " refuted=" << refuted << " us="
                    << std::chrono::duration_cast<std::chrono::microseconds>(
                        std::chrono::steady_clock::now() - started).count() << '\n';
            }
            if (refuted) {
#ifdef XOLVER_ENABLE_CASESTATS
                finalizeCaseStats(Result::Unsat, 0.0, nullptr, nullptr, cadicalBackend);
#endif
                return Result::Unsat;
            }
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
        // Applies to pure QF_NIA and to LIA whose integer domains are proved
        // binary by positive root facts (no real/UF/array/DT/mixed). Iter-3/4/5
        // confirmed the CDCL(T)-per-atom-assignment bit-blast cannot close
        // the leipzig / VeryMax cluster because each per-call constraint
        // subset enumerates Boolean disjunct choices serially. The eager
        // path encodes the OR atoms directly into the bit-blast CNF so
        // CaDiCaL searches disjuncts + integer bits concurrently: leipzig
        // term-0Hb4yp.smt2 falls from 5 s TO to 152 ms (~33x). Held-out
        // 16-case set (oracle=SAT ∧ BLAN=SAT<10s ∧ xolver=TO) gains 4+/16.
        //
        // -------------------------------------------------------------------
        {
            if (xolver::config::read<xolver::config::ReadKind::Presence>("NIA_EAGER_BB_GATE_DIAG")) {
                std::cerr << "[EAGER-GATE] logic=" << logic
                          << " hasRealVar=" << features.hasRealVar
                          << " hasMixedIntReal=" << features.hasMixedIntReal
                          << " hasUF=" << features.hasUF
                          << " hasArray=" << features.hasArray
                          << " hasDatatype=" << features.hasDatatype
                          << " hasNonlinear=" << features.hasNonlinear
                          << "\n";
            }
            const bool binaryLinear = (logic == "QF_LIA" || logic == "LIA");
            const bool logicOk = (logic == "QF_NIA" || logic == "NIA" || binaryLinear);
            if (logicOk &&
                !features.hasRealVar && !features.hasMixedIntReal &&
                !features.hasUF && !features.hasArray && !features.hasDatatype) {
                phase("eager-bb-start");
                bitblast::EagerBitBlastSolver eagerbb;
                // Farkas/termination routing: eager-bb diverges on the
                // bilinear-λ width search of Stroeder/VeryMax UNSAT cases. When
                // the bounded-B refutation lane is opted in and the formula IS
                // Farkas-Or-shaped (bounded template coeffs + Farkas branches),
                // give eager-bb only a SHORT slice so it bails to Unknown and the
                // NIA pipeline's bounded-B refutation gets the UNSAT — while the
                // SAT cases, which eager-bb solves fast, still land in time.
                // PROMOTED default-ON (2026-06-08): the bounded-B refutation is
                // now a default NIA stage, so this routing must always engage —
                // otherwise eager-bb hogs the wall-clock and the refutation never
                // runs. The detector bails on non-Farkas inputs (good()==false),
                // so the cost there is one O(tree) scan.
                if (!binaryLinear) {
                    farkas::FarkasOrDetector fdet(*ir);
                    auto fprof = fdet.detect();
                    if (fprof.good() && !fprof.boundedGlobals.empty()) {
                        // Do NOT starve eager-bb on Farkas SAT: keep its FULL normal
                        // wall-clock share (pct = the general 33% default). eager-bb's
                        // consecutive-UNSAT cap bails it early on the UNSAT shapes
                        // (loop3 ~40s) and the refutation is fast, so a full share
                        // still leaves ample time for the UNSAT path while preserving
                        // every bit-blast SAT win. absMs is the dev-only fallback used
                        // when no wall-clock deadline is set (bash `timeout`), where
                        // the cap fires later than the small dev timeout.
                        eagerbb.setFarkasBudget(
                            config::read<config::ReadKind::Long>("XOLVER_NIA_FARKAS_EAGER_PCT", 33),
                            config::read<config::ReadKind::Long>("XOLVER_NIA_FARKAS_EAGER_BUDGET_MS", 2000));
                    }
                }
                auto eagerRoots = ir->assertions();
                eagerRoots.insert(eagerRoots.end(), assumptionIndicators.begin(), assumptionIndicators.end());
                eagerRoots.insert(eagerRoots.end(), indicatorRoots_.begin(), indicatorRoots_.end());
                auto ibr = binaryLinear ? eagerbb.solveBinary(*ir, eagerRoots)
                                        : eagerbb.solve(*ir, eagerRoots);
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
                    // Bool model (now exported by EagerBitBlast). Without this,
                    // ModelConverter::evalBool defaulted missing Bool vars to
                    // false, producing wrong Ite-branch selection in reconstruct.
                    for (const auto& [name, bval] : ibr.boolModel) {
                        lastModel_->assignments.emplace(name, bval ? "true" : "false");
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
                    // Merge note (eqnia <- integration): ALSO restore UCP-pinned
                    // vars. reconstruct() above replays ModelConverter steps
                    // (SolveEqs / UnconstrainedElim); mergeFixedBindings() replays
                    // the *separate* fixedBindings_ map for `(= var const)` atoms
                    // folded to true by UCP. Distinct elimination paths — both
                    // needed so get-model is complete on the EAGER Sat path.
                    mergeFixedBindings();
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
        auto setupResult = setupSolvers(
            logic, features, ir.get(), registry, theoryManager,
            sharedTermRegistry_, boolSortId_);

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

        // Wire the DT model re-validator: hand the EUF solver a pointer to
        // the original-formula assertions so its Full-effort check can
        // independently re-evaluate them under the candidate e-graph. Sound
        // floor for the QF_DT blocksworld false-SAT residual class (deep
        // BMC ITE-chain violations that modelFullyDetermined accepts).
        // Pointer outlives the solver (originalAssertions_ is a member).
        // Polymorphic: the hook is a no-op on every theory but the EUF solver.
        if (auto* euf = theoryManager.solverFor(TheoryId::EUF)) {
            euf->setOriginalAssertions(&originalAssertions_);
        }

        // Connect propagator FIRST (required before addObservedVar)
        CadicalTheoryPropagator propagator(registry, theoryManager, lemmaDb, *cadicalBackend);
        propagator.setUnknownReasonSink(&lastUnknownReason_);

        // One-step control: if a user Propagator is registered, wire it for
        // per-decision forwarding. The observable-atom set (onSetup) is built
        // lazily on the propagator's first callback — at construction time the
        // observed vars are not registered yet (addObservedVar runs below).
        // No-op when none is set (the default search path is untouched).
        if (userPropagator_) {
            propagator.setUserPropagator(userPropagator_, contextId_);
        }
#ifdef XOLVER_ENABLE_CASESTATS
        propagator.setCaseStats(&caseStats_);
        if (!dumpStatsPath_.empty()) {
            // Base path without extension for heartbeat
            propagator.setDumpStatsBasePath(dumpStatsPath_);
        }
#endif
        cadicalBackend->connectPropagator(&propagator);
        struct DisconnectPropagator {
            CadicalBackend& backend;
            ~DisconnectPropagator() { backend.disconnectPropagator(); }
        } connectionGuard{*cadicalBackend};

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
            // Use the same domain selection as the solver factory, including
            // constant arithmetic left behind by variable elimination.
            atomizer.setDefaultTheory(featureArithmeticTheory(features));
            if (polyKernelRaw) atomizer.setPolynomialKernel(polyKernelRaw);
        }

        // subformula (each assertion is a positive root) so the monotone
        // connectives below emit only the required half of their definition.
        phase("setup-done");
        // Farkas-Or Phase 0 hook: dump pre-atomization structural profile
        // to a file (env XOLVER_NIA_FARKAS_DUMP=1 enables; output goes to
        // XOLVER_NIA_FARKAS_DUMP_FILE or /tmp/farkas_dump). Pure
        // diagnostic — no behavioral change to the solve.
        if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_FARKAS_DUMP")) {
            const auto path = xolver::config::read<xolver::config::ReadKind::Path>("XOLVER_NIA_FARKAS_DUMP_FILE", "/tmp/farkas_dump");
            FILE* fdump = std::fopen(path.c_str(), "a");
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

        // Assumption-based unsat-core (checkSatAssuming). Atomize each assumption
        // so its atom becomes theory-observed (atomize → registry → addObservedVar),
        // and collect the literals to ASSUME — we do NOT add them as clauses, so
        // they enter the solve as retractable CaDiCaL assumptions and failed() can
        // report the minimized core on UNSAT. assumptionRoots_ is empty on a plain
        // checkSat, so assumptionLits stays empty and the solve path is unchanged.
        std::vector<SatLit> assumptionLits;
        std::vector<Term> assumptionReportTerms;  // parallel: Term to report if lit fails
        // API assumptions (checkSatAssuming): report the assumption itself.
        for (size_t k = 0; k < assumptionIndicators.size(); ++k) {
            ExprId aRoot = assumptionIndicators[k];
            assumptionLits.push_back(atomizer.atomize(aRoot, *ir));
            assumptionReportTerms.push_back(Term(assumptionRoots_[k], contextId_));
        }
        // File-level indicators (:produce-unsat-cores): report the ORIGINAL assertion.
        for (size_t k = 0; k < indicatorRoots_.size(); ++k) {
            assumptionLits.push_back(atomizer.atomize(indicatorRoots_[k], *ir));
            assumptionReportTerms.push_back(indicatorCoreTerms_[k]);
        }

        // Compile branch-independent relations for multi-predicate threshold
        // families once. Isolated pairs retain ordinary explained theory
        // conflicts, limiting preprocessing's effect on Boolean search.
        BoundAxiomGenerator::generate(registry, *sat, TheoryId::LIA, 3);
        phase("bound-axioms-done");

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

        // Bounded brute-force model-construction pre-pass for UFNIA. CMS
        // enumerates low-height candidate assignments and DERIVES UF-app values
        // by functional consistency (pow2(k)@k=1 == pow2(1)); it re-validates
        // every model against the original assertions and never emits UNSAT, so a
        // no-model run just falls through to the main solve. Bit-width-independent
        // UFNIA (pow2(k)) otherwise bit-blasts into an OOM the post-solve recovery
        // never reaches, so this must run BEFORE the solve. Brute force => HARD-
        // bounded, but NOT tuned to this dev machine: the competition server is
        // slower, so a value sized to dev-machine timing would lose wins there.
        // The machine-INDEPENDENT bound is the candidate cap (2M assignments —
        // same work on any CPU); the wall-clock is a generous 3s safety backstop
        // (~0.25% of the 20-min competition budget) for pathological per-candidate
        // cost, not the binding limit for the recovered witnesses. Default-ON for
        // QF_UFNIA only.
        bool cmsPrePassFound = false;
        bool prepassEnabled = (logic == "QF_UFNIA" || logic == "UFNIA");
        if (prepassEnabled) {
            CandidateModelSearch::Config cfg;
            cfg.assertionRootsOverride = originalAssertions_;
            cfg.wallClockBudget = std::chrono::milliseconds(3000);
            cfg.maxCandidatesPerStrategy = 2000000;
            CandidateModelSearch cms(*ir, logic, cfg);
            auto pre = cms.run();
            if (pre.found) {
                lastModel_ = pre.model;
                cmsPrePassFound = true;
            }
        }

        // Bit-width INSTANTIATION probe. DEFAULT-ON for QF_UFNIA.
        // Zohar bit-width-encoded QF_UFNIA (pow2 UF) has a free symbolic width
        // var k; CMS's global height-first search burns its budget on small k
        // (which have NO witness) before reaching the witness width, so a SAT
        // case that solves instantly at a pinned k (e.g. int_check shl/lshr:
        // k>=5 -> sat in 0.2s) times out when k is free. Detect the width var
        // (the `(>= k 1)` signature + pinned-pow2 args) and probe small concrete
        // widths/shifts: run CMS on (original ∧ (= k w)). SOUND: a model of the
        // constrained formula is a model of the original (the extra conjunct only
        // restricts), and CMS validates every candidate — so this is SAT-only and
        // can never emit a wrong answer; it runs only when the normal CMS pre-pass
        // found nothing, and is a near-no-op when no width var is detected (e.g.
        // certora's concrete-2^256 cases). Measured net-positive, 0-regress,
        bool widthProbeOn = (logic == "QF_UFNIA" || logic == "UFNIA");

        if (!cmsPrePassFound && widthProbeOn) {
            const SortId intSort = ir->intSortId();
            const SortId boolSort = ir->boolSortId();
            auto constVal = [&](ExprId x, mpq_class& out) -> bool {
                const auto& n = ir->get(x);
                if (n.kind == Kind::ConstInt) {
                    if (auto* p = std::get_if<int64_t>(&n.payload.value)) { out = *p; return true; }
                    if (auto* s = std::get_if<std::string>(&n.payload.value)) { out = mpq_class(*s); return true; }
                } else if (n.kind == Kind::ConstReal) {
                    if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                        mpq_class q(*s);
                        if (q.get_den() == 1) { out = q; return true; }
                    }
                }
                return false;
            };
            // Pinned functions: f with a top-level (= (f const...) c) base case
            // (the pow2 base cases). Their VARIABLE arguments are the encoding's
            // free width/shift vars (k in pow2(k), s in pow2(s)).
            std::unordered_set<std::string> pinnedFuncs;
            std::unordered_set<ExprId> pseen;
            std::function<void(ExprId)> findPinned = [&](ExprId e) {
                if (!pseen.insert(e).second) return;
                const auto& n = ir->get(e);
                if (n.kind == Kind::Eq && n.children.size() == 2) {
                    for (ExprId side : {n.children[0], n.children[1]}) {
                        const auto& s = ir->get(side);
                        if (s.kind == Kind::UFApply) {
                            bool allConst = !s.children.empty();
                            for (ExprId a : s.children) { mpq_class cv; if (!constVal(a, cv)) { allConst = false; break; } }
                            if (allConst)
                                if (auto* fn = std::get_if<std::string>(&s.payload.value)) pinnedFuncs.insert(*fn);
                        }
                    }
                }
                for (ExprId c : n.children) findPinned(c);
            };
            for (ExprId r : originalAssertions_) findPinned(r);

            // Probe vars, ORDERED: strict-positive-lower-bound (width) vars first,
            // then VARIABLE args of pinned-function applications (shift vars).
            std::vector<ExprId> probeVars;
            std::unordered_set<ExprId> probeSet, scanSeen;
            auto addProbe = [&](ExprId v) {
                if (ir->get(v).kind == Kind::Variable && ir->get(v).sort == intSort &&
                    probeSet.insert(v).second)
                    probeVars.push_back(v);
            };
            std::function<void(ExprId, bool)> scan = [&](ExprId e, bool widthPass) {
                if (!scanSeen.insert(e).second) return;
                const auto& n = ir->get(e);
                if (widthPass && n.children.size() == 2 &&
                    (n.kind == Kind::Gt || n.kind == Kind::Geq ||
                     n.kind == Kind::Lt || n.kind == Kind::Leq)) {
                    ExprId a = n.children[0], b = n.children[1]; mpq_class cv;
                    if ((n.kind == Kind::Gt || n.kind == Kind::Geq) &&
                        ir->get(a).kind == Kind::Variable && constVal(b, cv) &&
                        cv >= (n.kind == Kind::Geq ? 1 : 0)) addProbe(a);
                    else if ((n.kind == Kind::Lt || n.kind == Kind::Leq) &&
                             ir->get(b).kind == Kind::Variable && constVal(a, cv) &&
                             cv >= (n.kind == Kind::Leq ? 1 : 0)) addProbe(b);
                }
                if (!widthPass && n.kind == Kind::UFApply)
                    if (auto* fn = std::get_if<std::string>(&n.payload.value))
                        if (pinnedFuncs.count(*fn))
                            for (ExprId c : n.children) addProbe(c);
                for (ExprId c : n.children) scan(c, widthPass);
            };
            for (ExprId r : originalAssertions_) scan(r, true);   // width vars first
            scanSeen.clear();
            for (ExprId r : originalAssertions_) scan(r, false);  // then shift vars
            if (probeVars.size() > 2) probeVars.resize(2);        // bound the grid
            if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_CMS_WIDTH_PROBE_DIAG"))
                std::fprintf(stderr, "[WPROBE] pinnedFuncs=%zu probeVars=%zu\n",
                             pinnedFuncs.size(), probeVars.size()), std::fflush(stderr);

            auto makeEq = [&](ExprId v, int w) -> ExprId {
                TermExpr cN; cN.kind = Kind::ConstInt; cN.sort = intSort;
                cN.payload.value = static_cast<int64_t>(w);
                TermExpr eqN; eqN.kind = Kind::Eq; eqN.sort = boolSort;
                eqN.children.push_back(v); eqN.children.push_back(ir->addShared(cN));
                return ir->addShared(eqN);
            };
            auto tryRoots = [&](const std::vector<ExprId>& extra) {
                CandidateModelSearch::Config wcfg;
                wcfg.assertionRootsOverride = originalAssertions_;
                for (ExprId e : extra) wcfg.assertionRootsOverride.push_back(e);
                wcfg.wallClockBudget = std::chrono::milliseconds(300);
                wcfg.maxCandidatesPerStrategy = 2000000;
                CandidateModelSearch wcms(*ir, logic, wcfg);
                auto wp = wcms.run();
                if (wp.found) { lastModel_ = wp.model; cmsPrePassFound = true; }
            };
            using clk = std::chrono::steady_clock;
            auto now = [] { return clk::now(); };
            static const int kWidths[] = {1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 24, 32};
            static const int widthSet[] = {1, 2, 3, 4, 5, 6, 8, 16};
            static const int shiftSet[] = {0, 1, 2, 3, 4};  // shift amounts are small
            // Phase 1: pin ONLY the width var (probeVars[0]) — cracks shl/urem-by-k
            // (bvslt_bvshl0, bvsgt_bvurem1). Own 4s deadline so it cannot starve
            // the pair phase. (Pinning the shift var alone never helps, so skip it.)
            const auto p1Deadline = now() + std::chrono::milliseconds(4000);
            if (!probeVars.empty()) {
                for (int w : kWidths) {
                    if (cmsPrePassFound || now() > p1Deadline) break;
                    tryRoots({makeEq(probeVars[0], w)});
                }
            }
            // Phase 2: pin a (width, shift) PAIR — lshr/urem need both. The shift
            // var ranges over small amounts {0..4}; width over widthSet. Own 8s
            // deadline. (4,2)/(5,1) witnesses are reached well within budget.
            const auto p2Deadline = now() + std::chrono::milliseconds(8000);
            if (!cmsPrePassFound && probeVars.size() == 2) {
                for (int w0 : widthSet) {
                    if (cmsPrePassFound || now() > p2Deadline) break;
                    ExprId e0 = makeEq(probeVars[0], w0);
                    for (int w1 : shiftSet) {
                        if (cmsPrePassFound || now() > p2Deadline) break;
                        tryRoots({e0, makeEq(probeVars[1], w1)});
                    }
                }
            }
        }

        auto solveT0 = std::chrono::steady_clock::now();
        auto result = cmsPrePassFound ? SatSolver::SolveResult::Sat
                    : (assumptionLits.empty() ? sat->solve()
                                              : sat->solve(assumptionLits));
        auto solveT1 = std::chrono::steady_clock::now();
        [[maybe_unused]] auto solveDurMs = std::chrono::duration_cast<std::chrono::microseconds>(solveT1 - solveT0).count() / 1000.0;

        // Extract the assumption-based unsat-core (the failed assumptions) WHILE
        // CaDiCaL still holds the post-solve state, before disconnectPropagator()
        // below. getFailedAssumptions() returns a subset of the exact lits we
        // passed; map each back to its assumption root Term. An empty failed set
        // (UNSAT proven without the assumptions) leaves the conservative full-set
        // core seeded by checkSatAssuming. Sound, possibly non-minimal.
        // Best-effort core MINIMIZATION via failed(), RESTRICTED to theories where
        // it is validated-reliable. failed() reports the assumptions used in the
        // boolean conflict; for single-sort linear / UF / array logics this is a
        // sound core (corpus-validated by tools/check_unsat_core.py — 0 insufficient
        // across lia/lra/euf). But for NONLINEAR or MIXED int/real reasoning, the
        // theory can derive a conflict whose explanation under-reports the
        // contributing assertions (NIA substituting x=0; mixed-sort atom desync),
        // yielding an INSUFFICIENT core — and Xolver's theory solvers are
        // incremental, so an in-context re-solve cannot validate it (stale tableau/
        // e-graph). There we KEEP the conservative full set seeded before the solve
        // (always a valid core — the problem is UNSAT); reliable minimal cores for
        // those logics need proof tracking (Track C2) or external deletion
        // (check_unsat_core.py --minimize). Soundness-first: never emit a core we
        // cannot stand behind.
        if (!assumptionLits.empty() && result == SatSolver::SolveResult::Unsat &&
            !features.hasNonlinear && !features.hasMixedIntReal) {
            std::vector<SatLit> failed = sat->getFailedAssumptions();
            std::vector<Term> core;
            core.reserve(failed.size());
            for (SatLit fl : failed) {
                for (size_t k = 0; k < assumptionLits.size(); ++k) {
                    if (assumptionLits[k] == fl) {
                        core.push_back(assumptionReportTerms[k]);
                        break;
                    }
                }
            }
            if (!core.empty()) lastUnsatCore_ = std::move(core);
        }

        // Capture boolean VARIABLE values from the SAT assignment WHILE the
        // model is still live (disconnecting the propagator below invalidates
        // CaDiCaL's val()). Theory models survive disconnect because they are
        // captured via the propagator's assignment view, but pure-boolean vars
        // are not theory-tracked. Used by the strict-validation gate.
        std::unordered_map<std::string, std::string> boolVarVals;
        // Skip SAT-var readback when the CMS pre-pass produced the model: the SAT
        // solver was never run (CaDiCaL val() would abort), and the CMS model is
        // already complete + validated.
        if (result == SatSolver::SolveResult::Sat && !cmsPrePassFound) {
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

        // Disconnecting CaDiCaL can notify a backtrack/reset and discard
        // active simplex bounds. Freeze the model first: choosing a concrete
        // infinitesimal after that reset can falsify strict inequalities.
        std::optional<TheorySolver::TheoryModel> solvedTheoryModel;
        if (result == SatSolver::SolveResult::Sat && !cmsPrePassFound)
            solvedTheoryModel = theoryManager.getModel();
        cadicalBackend->disconnectPropagator();
        propagator.stats().print(std::cerr);

        Result ret = Result::Unknown;
        if (result == SatSolver::SolveResult::Sat) {
            // Keep the CMS pre-pass model (already validated); only pull the
            // theory model on the normal solve path.
            if (!cmsPrePassFound) lastModel_ = std::move(solvedTheoryModel);
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
            // Original-formula validation must see eliminated definitions and
            // strict-bound witnesses before inspecting a candidate model.
            // The final replay remains necessary if a later repair replaces it.
            if (lastModel_ && !modelConverter_.empty())
                modelConverter_.reconstruct(lastModel_->numericAssignments,
                                           lastModel_->assignments, *ir);
            if (features.hasArray && lastModel_)
                completeArrayModel(*ir, originalAssertions_, *lastModel_);
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
        if (ret == Result::Sat && (modelRequestedImpl() || !divModOrigins_.empty())) {
            buildPartialFuncModel();
            if (partialFuncModel_.inconsistent ||
                (modelRequestedImpl() && partialFuncModel_.realDivByZero)) {
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

        // NOTE: datatype sat soundness is enforced precisely inside the theory
        // layer (EufSolver::satComplete blocks a sat unless every datatype
        // e-class has a determined constructor — a concrete ground-term model).
        // No blanket DT-sat floor here: a fully-determined consistent DT model
        // is a sound sat; only constructor-undetermined cases fall through to
        // Unknown via satComplete.

        // Positively validate candidates from incomplete integer solving.
        bool niaSatFloor = features.hasNonlinear && !features.hasRealVar;
        // Div/mod-by-constant is LINEAR (hasNonlinear=false), so it slips past
        // the nonlinear floor above -- yet the div/mod lowering can yield a
        // spurious sat whose model satisfies the lowered linear-mod system but
        // not the original mod relations (e.g. SVCOMP soft_float: many
        // (mod m 2^k) clauses; xolver=sat, oracle=unsat). Validate the sat for
        // such (pure-Int) div/mod-lowered formulas too. Sound: only sat->unknown.
        // Explicit zero-divisor interpretations also permit checking the UF
        // combination against the original mathematical-integer formula.
        bool divModSatFloor = !divModOrigins_.empty() &&
                              !features.hasRealVar;
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
        bool realDivPurifySatFloor = features.hasNonlinear && features.hasRealVar &&
                                     hasRealDivisionInOriginal();
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
        // Require positive validation for arithmetic/array combinations.
        auto isCombArrayLogic = [](const std::string& L) {
            return L == "QF_ALIA" || L == "ALIA" || L == "QF_ALRA" || L == "ALRA" ||
                   L == "QF_AUFLIA" || L == "AUFLIA" || L == "QF_AUFLRA" || L == "AUFLRA";
        };
        bool arrayCombSatFloor = features.hasArray && isCombArrayLogic(logic);
        bool validateSat = niaSatFloor || divModSatFloor || realDivPurifySatFloor ||
                           arrayCombSatFloor;
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
        if (ret == Result::Sat && !divModOrigins_.empty()) {
            buildPartialFuncModel();
            if (partialFuncModel_.inconsistent) {
                lastUnknownReason_ = "partial-function model: inconsistent reconstructed extension";
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

} // namespace xolver
