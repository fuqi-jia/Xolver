#include "api/SolverImpl.h"

namespace xolver {

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

// #19/#49 native-crash firewall: libpoly / GMP can SIGSEGV / SIGABRT / SIGFPE deep
// in real-algebraic computation on degenerate inputs (a class the C++ try/catch
// below cannot intercept — signals are not exceptions). When enabled, a synchronous
// crash during the solve siglongjmps back and the verdict becomes Unknown (SOUND —
// an incomplete answer, never a wrong one), preserving the process so the
// regression runner / incremental API survive a single bad case instead of dying.
// The signal is synchronous, so it is delivered to the faulting (solve) thread; the
// jmp_buf + active flag are thread_local so the handler resolves to that thread's
// recovery point. Default-OFF: XOLVER_SIGNAL_FIREWALL=1 to enable.
namespace {
thread_local sigjmp_buf g_solveCrashJmp;
thread_local volatile sig_atomic_t g_solveCrashActive = 0;
void solveCrashHandler(int sig) {
    if (g_solveCrashActive) {
        g_solveCrashActive = 0;
        siglongjmp(g_solveCrashJmp, sig);
    }
    // Not inside a guarded solve — restore default disposition and re-raise so a
    // genuine crash outside the firewall is NOT masked.
    std::signal(sig, SIG_DFL);
    std::raise(sig);
}
}  // namespace

Result Solver::checkSat() {
    // Start the global solve wall-clock so per-engine budgets can scale to the
    // time remaining (P0-A). Unset / 0 => no deadline => no behavior change.
    wall::beginSolve(env::paramLong("XOLVER_WALLCLOCK_MS", 0));
    Result r;
    // Non-static: re-read per solve so per-call control works (one getenv/solve is
    // negligible) and so a unit test can toggle the firewall between checkSat calls.
    const bool sigFirewall = env::diag("XOLVER_SIGNAL_FIREWALL");
    struct sigaction oldSegv{}, oldAbrt{}, oldFpe{};
    bool fwInstalled = false;
    if (sigFirewall) {
        if (sigsetjmp(g_solveCrashJmp, 1) != 0) {
            // Recovered from a native crash mid-solve.
            if (fwInstalled) {
                sigaction(SIGSEGV, &oldSegv, nullptr);
                sigaction(SIGABRT, &oldAbrt, nullptr);
                sigaction(SIGFPE, &oldFpe, nullptr);
            }
            g_solveCrashActive = 0;
            pImpl->lastUnknownReason_ =
                "native crash (signal) during solve — firewalled to Unknown";
            pImpl->lastModel_.reset();
            wall::endSolve();
            return Result::Unknown;
        }
        struct sigaction sa{};
        sa.sa_handler = solveCrashHandler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = SA_NODEFER;
        sigaction(SIGSEGV, &sa, &oldSegv);
        sigaction(SIGABRT, &sa, &oldAbrt);
        sigaction(SIGFPE, &sa, &oldFpe);
        fwInstalled = true;
        g_solveCrashActive = 1;
    }
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
        // Test-only hook to exercise the native-crash firewall (#19/#49). Gated by
        // an env var no production path sets; raises a synchronous SIGSEGV inside
        // the guarded region so the firewall's recover-to-Unknown can be tested.
        if (env::diag("XOLVER_TEST_FORCE_CRASH")) {
            volatile int* p = nullptr;
            *p = 1;  // SIGSEGV
        }
        int ebsRounds = env::paramInt("XOLVER_ESCALATING_BOUNDED_SAT", 0);
        if (ebsRounds > 0 && !std::getenv("XOLVER_STRAT_PORTFOLIO")) {
            int budget = env::paramInt("XOLVER_ESCALATING_BOUNDED_SAT_BUDGET_MS", 15000);
            r = pImpl->checkSatEscalatingBoundedSat(ebsRounds, budget);
        } else {
            r = std::getenv("XOLVER_STRAT_PORTFOLIO")
                    ? pImpl->checkSatPortfolio()
                    : pImpl->checkSatInternal();
        }
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
    if (fwInstalled) {
        g_solveCrashActive = 0;
        sigaction(SIGSEGV, &oldSegv, nullptr);
        sigaction(SIGABRT, &oldAbrt, nullptr);
        sigaction(SIGFPE, &oldFpe, nullptr);
    }
    wall::endSolve();
    return r;
}

Result Solver::checkSatAssuming(std::vector<Term> assumptions) {
    pImpl->lastAssumptions_ = assumptions;
    // Sound fallback core: until the SAT layer reports a minimized subset, the
    // whole assumption set is a valid (if non-minimal) core.
    pImpl->lastUnsatCore_ = assumptions;

    // Preferred path (hard assertions present): pass the assumptions to the SAT
    // core as real assumption LITERALS rather than asserting them. Each
    // assumption atom is observed by the theory via atomize, CaDiCaL assumes its
    // literal, and on UNSAT failed() yields the MINIMIZED core (see
    // checkSatInternal). Not mutating the assertion list means lowering can never
    // rewrite an assumption, and getUnsatCore() returns the true failing subset.
    const bool haveHardAssertions = pImpl->ir && !pImpl->ir->assertions().empty();
    if (haveHardAssertions) {
        pImpl->assumptionRoots_.clear();
        pImpl->assumptionRoots_.reserve(assumptions.size());
        for (Term a : assumptions) pImpl->assumptionRoots_.push_back(a.id());
        Result r = checkSat();
        pImpl->assumptionRoots_.clear();
        return r;
    }

    // Degenerate path (no hard assertions): the SAT-assumption route would have
    // nothing to drive theory setup / would short-circuit on the empty assertion
    // set. Fall back to the original behavior — assert the assumptions as
    // formulas so the worker reaches a real solve — giving the correct verdict
    // with the conservative full-set core (no minimization, but no regression).
    push();
    for (Term a : assumptions) assertFormula(a);
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
    if (!pImpl) return {};
    // Assumption-based core: the minimized subset of the checkSatAssuming
    // assumptions that CaDiCaL's failed() reported as necessary for UNSAT
    // (falls back to the full assumption set when no SAT-level minimization was
    // available, e.g. UNSAT proven in preprocessing). Sound, possibly
    // non-minimal. Meaningful only after checkSatAssuming() returned Unsat.
    return pImpl->lastUnsatCore_;
}

bool Solver::unsatCoreRequested() const {
    if (!pImpl) return false;
    auto it = pImpl->options.find("produce-unsat-cores");
    if (it != pImpl->options.end() && it->second.kind == OptionValue::Bool &&
        it->second.b)
        return true;
    if (!pImpl->parser) return false;
    auto opts = pImpl->parser->getOptions();
    return opts && opts->get_unsat_core;
}

void Solver::dumpUnsatCore(std::ostream& os) const {
    // SMT-LIB get-unsat-core response shape: a parenthesized list. We emit the
    // ORIGINAL assertions that form the core as SMT-LIB terms (Xolver gates each
    // assertion with an indicator; :named-name output is a future enhancement
    // needing the parser to expose its named-assertion map).
    os << "(";
    if (pImpl && pImpl->ir) {
        const auto& core = pImpl->lastUnsatCore_;
        for (size_t i = 0; i < core.size(); ++i) {
            os << (i ? " " : "") << dumpExprToSMT2(core[i].id(), *pImpl->ir);
        }
    }
    os << ")\n";
}

bool Solver::modelRequested() const {
    if (!pImpl || !pImpl->parser) return false;
    auto opts = pImpl->parser->getOptions();
    return opts && opts->get_model;
}

std::vector<Solver::ScriptResponseCommand> Solver::scriptResponseCommands() const {
    std::vector<ScriptResponseCommand> out;
    if (!pImpl || !pImpl->parser) return out;
    using K = ScriptResponseCommand::Kind;
    const auto& cmds = pImpl->parser->getScript().commands();
    for (size_t i = 0; i < cmds.size(); ++i) {
        const auto& cmd = cmds[i];
        switch (cmd.type) {
            case SOMTParser::CMD_TYPE::CT_ECHO:
                out.push_back({K::Echo, cmd.keyword, i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_INFO:
                out.push_back({K::GetInfo, cmd.keyword, i}); break;
            case SOMTParser::CMD_TYPE::CT_CHECK_SAT:
            case SOMTParser::CMD_TYPE::CT_CHECK_SAT_ASSUMING:
                out.push_back({K::CheckSat, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_VALUE:
                out.push_back({K::GetValue, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_MODEL:
                out.push_back({K::GetModel, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_ASSIGNMENT:
                out.push_back({K::GetAssignment, "", i}); break;
            default: break;
        }
    }
    return out;
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

std::string Solver::getValueResponse(size_t scriptIndex) const {
    if (!pImpl || !pImpl->parser || !pImpl->lastModel_) return {};
    const auto& cmds = pImpl->parser->getScript().commands();
    if (scriptIndex >= cmds.size()) return {};
    const auto& cmd = cmds[scriptIndex];
    if (cmd.type != SOMTParser::CMD_TYPE::CT_GET_VALUE) return {};
    const auto& model = *pImpl->lastModel_;
    std::string out = "(";
    for (const auto& t : cmd.value_terms) {
        if (!t) return {};
        std::string val;
        if (t->isVBool() || t->isVInt() || t->isVReal()) {
            auto it = model.assignments.find(t->getName());
            if (it == model.assignments.end()) return {};  // unassigned -> bail
            SortKind sk = t->isVBool() ? SortKind::Bool
                        : t->isVInt()  ? SortKind::Int
                                       : SortKind::Real;
            val = formatModelValue(sk, it->second);
        } else if (t->isConst()) {
            val = SOMTParser::dumpSMTLIB2(t);  // a literal evaluates to itself
        } else {
            return {};  // compound / unsupported term -> emit nothing (no wrong value)
        }
        out += "(" + SOMTParser::dumpSMTLIB2(t) + " " + val + ")";
    }
    out += ")";
    return out;
}

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

void Solver::dumpFeatures(std::ostream& os) const {
    if (!pImpl || !pImpl->ir) { os << "{}\n"; return; }
    const CoreIr& ir = *pImpl->ir;
    LogicFeatures f = LogicFeatureDetector(ir).detect();
    size_t nVars = 0;
    for (ExprId id = 0; id < static_cast<ExprId>(ir.size()); ++id)
        if (ir.get(id).kind == Kind::Variable) ++nVars;
    auto b = [](bool v) { return v ? "true" : "false"; };
    os << "{\"logic\":\"" << pImpl->logic << "\""
       << ",\"asserts\":" << ir.assertions().size()
       << ",\"vars\":" << nVars
       << ",\"nodes\":" << ir.size()
       << ",\"nonlinear\":" << b(f.hasNonlinear)
       << ",\"mixed_int_real\":" << b(f.hasMixedIntReal)
       << ",\"int\":" << b(f.hasInt)
       << ",\"real\":" << b(f.hasReal)
       << ",\"array\":" << b(f.hasArray)
       << ",\"uf\":" << b(f.hasUF)
       << ",\"bv\":" << b(f.hasBV)
       << ",\"datatype\":" << b(f.hasDatatype)
       << ",\"quantifier\":" << b(f.hasQuantifier)
       << "}\n";
}

} // namespace xolver
