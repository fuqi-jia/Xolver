#include "api/SolverImpl.h"

namespace xolver {

// Relocated Solver::Impl method definitions (declared in SolverImpl.h).

void Solver::Impl::reset() {
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
bool Solver::Impl::parseFile(std::string_view filename) {
        parser = std::make_unique<SOMTParser::Parser>();
        // DIAG (XOLVER_NO_EXPAND_FUNCTIONS): toggle define-fun inlining to confirm
        // whether parse-time expansion is the Certora blowup. Not for production.
        parser->setOption("expand_functions",
                          !xolver::env::diag("XOLVER_NO_EXPAND_FUNCTIONS"));
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
CoreIr& Solver::Impl::ensureIr() {
        // Hash-cons is opt-in PER CALL-SITE via CoreIr::addShared() (nia-bb-3
        // 31fdaa8): parser / atomizer / ITE-lowerer keep add() (fresh ExprId,
        // so incremental push/pop stays sound), preprocess passes use addShared.
        // No global hash-cons knob — supersedes my XOLVER_IR_HASHCONS stopgap.
        if (!ir) ir = std::make_unique<CoreIr>();
        return *ir;
}
SortId Solver::Impl::getOrCreateBoolSort() {
        if (boolSortId_ != NullSort) return boolSortId_;
        auto& cir = ensureIr();
        boolSortId_ = cir.allocateSortId();
        cir.registerSort(boolSortId_, SortKind::Bool);
        cir.setBoolSortId(boolSortId_);
        return boolSortId_;
}
SortId Solver::Impl::getOrCreateIntSort() {
        if (intSortId_ != NullSort) return intSortId_;
        auto& cir = ensureIr();
        intSortId_ = cir.allocateSortId();
        cir.registerSort(intSortId_, SortKind::Int);
        cir.setIntSortId(intSortId_);
        return intSortId_;
}
SortId Solver::Impl::getOrCreateRealSort() {
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
Result Solver::Impl::checkSatPortfolio() {
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
Result Solver::Impl::runArmWithBudget(int budgetMs) {
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
    // Extract an integer value from a ConstInt / int-valued ConstReal node.
bool Solver::Impl::extractIntConst(ExprId e, int64_t& out) const {
        const CoreExpr& n = ir->get(e);
        if (n.kind == Kind::ConstInt) {
            if (auto* p = std::get_if<int64_t>(&n.payload.value)) { out = *p; return true; }
        } else if (n.kind == Kind::ConstReal) {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                mpq_class q(*s);
                if (q.get_den() == 1) { out = q.get_num().get_si(); return true; }
            }
        }
        return false;
}
    // DERIVE the escalating fast-path's seed bound K0 from the constraints
    // (Cramer / small-model style) instead of guessing. A free integer var
    // coupled linearly to bounded vars satisfies |v| <= M / C, where
    //   M = max magnitude of the bounded vars' explicit bounds, and
    //   C = smallest nonzero coefficient the free vars are multiplied by (the
    //       resolution of the linear coupling, >= 1).
    // Returns K0 >= 1, or 0 if there is no free integer var (fast-path moot).
long Solver::Impl::deriveBoundSeed() const {
        if (!ir) return 0;
        SortId intSort = ir->intSortId();
        if (intSort == NullSort) return 0;
        std::unordered_set<ExprId> hasLower, hasUpper;
        int64_t maxBoundMag = 0;
        scanIntVarBounds(hasLower, hasUpper, maxBoundMag);
        std::unordered_set<ExprId> freeVars;
        for (ExprId id = 0; id < static_cast<ExprId>(ir->size()); ++id) {
            const CoreExpr& n = ir->get(id);
            if (n.kind == Kind::Variable && n.sort == intSort &&
                (!hasLower.count(id) || !hasUpper.count(id)))
                freeVars.insert(id);
        }
        if (freeVars.empty()) return 0;
        long M = maxBoundMag > 0 ? static_cast<long>(maxBoundMag) : 1;
        // C = min nonzero |coef| over Mul(freeVar, const) terms (>= 1).
        long C = 0;
        for (ExprId id = 0; id < static_cast<ExprId>(ir->size()); ++id) {
            const CoreExpr& n = ir->get(id);
            if (n.kind != Kind::Mul || n.children.size() != 2) continue;
            ExprId a = n.children[0], b = n.children[1];
            ExprId cstc = NullExpr;
            if (freeVars.count(a)) cstc = b;
            else if (freeVars.count(b)) cstc = a;
            if (cstc == NullExpr) continue;
            int64_t cv;
            if (extractIntConst(cstc, cv) && cv != 0) {
                long mag = cv < 0 ? -cv : cv;
                if (C == 0 || mag < C) C = mag;
            }
        }
        if (C < 1) C = 1;
        long K0 = (M + C - 1) / C;   // ceil(M / C)
        return K0 < 1 ? 1 : K0;
}
    // Add  (>= v (- K))  / (<= v K)  for the missing side of every integer
    // Variable that lacks an explicit constant bound there. Returns true iff at
    // least one bound was injected (false => no free integer var => fast-path
    // cannot help). Sound: bounds are only ADDED constraints.
bool Solver::Impl::injectFreeIntVarBounds(int K) {
        if (!ir) return false;
        SortId intSort = ir->intSortId();
        if (intSort == NullSort) return false;
        std::unordered_set<ExprId> hasLower, hasUpper;
        int64_t maxBoundMag = 0;
        scanIntVarBounds(hasLower, hasUpper, maxBoundMag);
        std::vector<ExprId> intVars;
        for (ExprId id = 0; id < static_cast<ExprId>(ir->size()); ++id) {
            const CoreExpr& n = ir->get(id);
            if (n.kind == Kind::Variable && n.sort == intSort) intVars.push_back(id);
        }
        SortId boolSort = getOrCreateBoolSort();
        ExprId loId = NullExpr, hiId = NullExpr;
        bool injected = false;
        for (ExprId v : intVars) {
            if (!hasLower.count(v)) {
                if (loId == NullExpr) {
                    CoreExpr loC; loC.kind = Kind::ConstInt; loC.sort = intSort;
                    loC.payload.value = static_cast<int64_t>(-K);
                    loId = ir->add(loC);
                }
                CoreExpr ge; ge.kind = Kind::Geq; ge.sort = boolSort;
                ge.children.push_back(v); ge.children.push_back(loId);
                ir->addAssertion(ir->add(ge));
                injected = true;
            }
            if (!hasUpper.count(v)) {
                if (hiId == NullExpr) {
                    CoreExpr hiC; hiC.kind = Kind::ConstInt; hiC.sort = intSort;
                    hiC.payload.value = static_cast<int64_t>(K);
                    hiId = ir->add(hiC);
                }
                CoreExpr le; le.kind = Kind::Leq; le.sort = boolSort;
                le.children.push_back(v); le.children.push_back(hiId);
                ir->addAssertion(ir->add(le));
                injected = true;
            }
        }
        return injected;
}
    // Sound escalating-bounded SAT fast-path (XOLVER_ESCALATING_BOUNDED_SAT=rounds).
    // The seed bound K0 is DERIVED from the constraints (deriveBoundSeed), not
    // guessed; for `rounds` rounds it solves  original ∪ {free-var bounds in
    // [-K, K]}  with K = K0, 2·K0, 4·K0, ...  A model of the bounded problem
    // satisfies the original (original ⊆ bounded), so a SAT verdict is a sound
    // witness. UNSAT of a box says NOTHING about the original (a witness may lie
    // outside) => escalate, never return UNSAT from the box. Closes formulas
    // whose only obstacle is an unbounded integer var with a bounded-magnitude
    // witness (e.g. GrandProduct β, |β| <= M/C). Needs a re-parseable source.
Result Solver::Impl::checkSatEscalatingBoundedSat(int rounds, int perKBudgetMs) {
        const std::string path = sourcePath_;  // reset() clears it; capture first
        if (path.empty()) return checkSatInternal();
        // Derive the seed bound K0 from the constraints (one parse).
        reset();
        if (!parseFile(path)) return Result::Unknown;
        long K0 = deriveBoundSeed();
        if (K0 <= 0) return checkSatInternal();   // no free int var -> no-op
        if (rounds < 1) rounds = 1;
        long K = K0;
        for (int r = 0; r < rounds; ++r, K *= 2) {
            reset();
            if (!parseFile(path)) return Result::Unknown;
            injectFreeIntVarBounds(static_cast<int>(K));
            if (runArmWithBudget(perKBudgetMs) == Result::Sat)
                return Result::Sat;  // sound witness for the original problem
            if (K > (1L << 30)) break;
        }
        // Box search exhausted -> one pristine normal solve (may be unsat/unknown).
        reset();
        if (!parseFile(path)) return Result::Unknown;
        return checkSatInternal();
}

} // namespace xolver
