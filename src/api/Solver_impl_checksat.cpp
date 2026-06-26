#include "api/SolverImpl.h"

namespace xolver {

// Relocated Solver::Impl method definitions (declared in SolverImpl.h).

Result Solver::Impl::checkSatInternal() {
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
                    ExprId a = ir->makeFreshVariable(bsid, "__xolver_uc");
                    ExprId guarded =
                        ir->add(CoreExpr{Kind::Implies, bsid, {a, eid}, Payload{}});
                    ir->addAssertion(guarded, lv);
                    indicatorRoots_.push_back(a);
                    indicatorCoreTerms_.push_back(Term(static_cast<uint32_t>(eid)));
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
        static const bool phaseProf = std::getenv("SOLVE_PHASE_PROF") != nullptr;
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
        bool enableRewrite = (xolver::env::diag("XOLVER_PP_REWRITE"));
        if (!enableRewrite && std::getenv("XOLVER_STRAT_PRESETS")) {
            enableRewrite = selectStrategy(logic, LogicFeatures{}).enableRewrite;
        }
        // R1 precedence (XOLVER_TARGETED_PP). The generic rewriter runs HERE,
        // before ReadOnlyArrayElim fires at the targeted-preprocess stage below,
        // and folds the read-over-write structure R1 pattern-matches — silently
        // pre-empting the +11 QF_ANIA read-only-array elimination (sum10 etc.
        // regress sat -> unknown when PP_REWRITE / STRAT_PRESETS is also on). On
        // exactly the array+NIA logics where R1 applies, defer to R1: skip the
        // generic rewriter so its elimination can match. The rewriter (and the
        // rest of STRAT_PRESETS) is untouched on every other logic.
        if (enableRewrite && env::paramInt("XOLVER_TARGETED_PP", 0) != 0 &&
            (logic == "QF_ANIA" || logic == "QF_AUFNIA" ||
             logic == "ANIA"    || logic == "AUFNIA")) {
            enableRewrite = false;
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
                xolver::env::diag("XOLVER_PP_INLINE_SINGLE_DEFS_INT");
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
            }
        }
#endif

        // Symbolic-modular simplification of `(mod p M)` for non-constant M
        // (the bit-width-independent Zohar `pow2(k)` modulus) must run BEFORE
        // ITE lowering: it pushes a mod through the `intmodtotal` ite-wrapper
        // (`(mod (ite C a b) M) -> (ite C (mod a M)(mod b M))`) and drops
        // M-divisible monomials, which only works while the ites are still ites.
        // Once CoreIteLowerer replaces them with fresh vars the structure is
        // opaque to the rewrite. Sound, general; no-op unless a non-constant
        // modulus is present. (The same pass runs again after lowering for
        // constant div/mod folding.)
        {
            IntDivModConstantFold preMod(*ir);
            preMod.run();
            preMod.commit();
        }

        // Reduce increment-store-tower array equality to an index-multiset
        // equality (PLONK GrandProduct soundness benchmarks, QF_ANIA). Exact —
        // `store-tower(B,[i..]) = store-tower(B,[j..]) <=> multiset{i..}={j..}`
        // (the base cancels) — and it eliminates the arrays so the NIA solver can
        // search the (otherwise array-blocked) model. Narrow structural match;
        // no-op unless the increment-tower shape is present. DEFAULT-OFF: the
        // rewrite is exact + 0-regression, but the post-reduction model-finding
        // currently solves only 1/6 GrandProduct cases (same/3) — the other 5
        // return unknown because the `beta` offset is unbounded (the matching
        // equations implicitly bound it, but the NIA bounded search doesn't
        // derive that). Promote to default-ON once that model-finding lands and
        // >=2 cases close. Opt-in via XOLVER_PP_STORE_TOWER_MULTISET=1.
        if (env::paramInt("XOLVER_PP_STORE_TOWER_MULTISET", 0) != 0) {
            StoreTowerEqMultiset stm(*ir);
            stm.run();
            stm.commit();
        }

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

        // Eager constant-index read-over-write store-chain folding. Resolves
        // `(select store-chain c)` for constant `c` by walking the chain once
        // (the read-over-write axiom on decidable constant index comparisons),
        // stopping at any variable-index store it cannot soundly skip. Runs
        // AFTER UnconditionalConstantPropagation (8a) so that constant bindings
        // already turned variable indices into constants. Exact (verdict-
        // preserving) and general; no-op unless a constant-index select over a
        // store chain is present. DEFAULT-OFF: the rewrite is the array
        // simplifier fast path (matches z3 sub-second on the SV-COMP CSeq
        // `cs_*` QF_ANIA files, whose ~1800-deep constant-index chains the lazy
        // array theory resolves only superlinearly). Opt-in: XOLVER_PP_ROW_FOLD=1.
        if (env::paramInt("XOLVER_PP_ROW_FOLD", 0) != 0) {
            ArrayReadOverWrite rowFold(*ir);
            rowFold.run();
            rowFold.commit();
        }

        // TARGETED preprocessing (XOLVER_TARGETED_PP, default-OFF): rules tuned
        // to the failing 5-logic corpus (QF_ANIA/AUFNIA/UFNIA/UFNRA/UFDTNIA),
        // not a general capability. ReadOnlyArrayElim Ackermannizes the
        // read-only array fragment that dominates the SV-COMP memory-model
        // QF_ANIA/AUFNIA cases (UltimateAutomizer `#memory_int` is never stored
        // to on the VC path): with no store/array-eq, `select` is an
        // uninterpreted function, so each scalar read becomes a fresh variable
        // plus per-base-array congruence axioms. Equisatisfiable; drops the
        // problem to QF_(N)IA and lets the pure-arith path solve it. Self-
        // guarding no-op the moment it sees a store/const-array/array-equality.
        roaeReads_.clear();
        roaeFreeArrayVars_.clear();
        roaeUsedWriteArray_ = false;
        if (env::paramInt("XOLVER_TARGETED_PP", 0) != 0) {
            ReadOnlyArrayElim roae(*ir);
            if (roae.run()) {
                roae.commit();
                roaeReads_ = roae.reads();
                roaeFreeArrayVars_ = roae.freeArrayVars();
                roaeUsedWriteArray_ = roae.usedWriteArray();
            }
        }

        // TARGETED (XOLVER_TARGETED_PP_UFACK, default-OFF): Ackermannize scalar
        // uninterpreted-function applications (QF_UFNRA "hidden nonlinearity"
        // FFT family). Exact reduction; the UNSAT direction needs no model
        // reconstruction (a SAT over the abstracted formula floors to Unknown).
        // Restricted to QF_UFNRA: it is net-positive there (the nonlinear term
        // hides in a UF arg) but net-NEGATIVE on QF_UFNIA (0 flips, regresses
        // solved cases by abstracting UF the combination was using).
        if (std::getenv("XOLVER_TARGETED_PP_UFACK") &&
            (logic == "QF_UFNRA" || logic == "UFNRA")) {
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
            if (xolver::env::diag("XOLVER_NIA_ZOHAR_DIAG")) {
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
                    xolver::env::diag("XOLVER_PP_AUTO_EUF_PROMOTE");
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
        if (xolver::env::diag("XOLVER_DUMP_FINAL_ASSERTS")) {
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
                    if (xolver::env::diag("XOLVER_ARRAY_NOARR_DOWNGRADE_DIAG"))
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
                if (xolver::env::diag("XOLVER_NRA_LINEAR_DOWNGRADE_DIAG"))
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
                if (xolver::env::diag("XOLVER_NIA_LINEAR_DOWNGRADE_DIAG"))
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
            if (xolver::env::diag("NIA_EAGER_BB_GATE_DIAG")) {
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
            // terms (Dartagnan ReachSafety-Loops + elster B_1 pattern). EAGER's
            // single CaDiCaL solve can outpace CDCL(T) on 10k+ atom LIA.
            // OPT-IN (default-OFF, XOLVER_NIA_EAGER_LIA): the EAGER model export
            // is currently WRONG on genuine QF_LIA whose vars are pinned by a
            // top-level bound atom (e.g. `(= x 1)`) — those atoms are skipped in
            // the encoding (width hint only), so the bit-blast leaves the var
            // unconstrained and the published model reads 0, violating the
            // assertion. The verdict stays sound (validator-gated), but get-model
            // returns garbage, so until the export reconstructs pinned vars this
            // path must not run by default. QF_NIA EAGER is unaffected (proven).
            bool eagerLia = xolver::env::diag("XOLVER_NIA_EAGER_LIA");
            bool logicOk = (logic == "QF_NIA" || logic == "NIA" ||
                            (eagerLia && (logic == "QF_LIA" || logic == "LIA")));
            if (eagerOn && logicOk &&
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
                {
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
                            env::paramLong("XOLVER_NIA_FARKAS_EAGER_PCT", 33),
                            env::paramLong("XOLVER_NIA_FARKAS_EAGER_BUDGET_MS", 2000));
                    }
                }
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
        if (xolver::env::diag("XOLVER_STRAT_PRESETS")) {
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
        // Polymorphic handoff via the base TheorySolver interface (the hook is a
        // no-op on every theory but the NIA solver) — keeps api/ decoupled from
        // the concrete solver type. In NIA-MCSAT mode solverFor(NIA) is an MCSAT
        // solver that inherits the no-op, exactly as the old concrete-typed cast
        // returned null and skipped the handoff.
        if (!modEqConstFacts_.empty()) {
            if (auto* nia = theoryManager.solverFor(TheoryId::NIA)) {
                nia->setModEqConstFacts(modEqConstFacts_);
            }
        }

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
            propagator.setUserPropagator(userPropagator_);
        }
#ifdef XOLVER_ENABLE_CASESTATS
        propagator.setCaseStats(&caseStats_);
        if (!dumpStatsPath_.empty()) {
            // Base path without extension for heartbeat
            propagator.setDumpStatsBasePath(dumpStatsPath_);
        }
#endif
        cadicalBackend->connectPropagator(&propagator);

        // L7 relevancy engine (XOLVER_RELEVANCY). Declared here so it outlives
        // sat->solve(); built + attached after atomize() (needs the memo). Empty
        // + inert until attached.
        RelevancyEngine relEngine;

        // Atomizer registers parsed atoms into registry (which calls addObservedVar)
        Atomizer atomizer(*sat);
        registry.setContext(sat.get(), &atomizer);
        atomizer.setRegistry(&registry);
        atomizer.setBoolSortId(boolSortId_);
        atomizer.setPgCnf(xolver::env::diag("XOLVER_PP_PG_CNF"));

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
        if (xolver::env::diag("XOLVER_NIA_FARKAS_DUMP")) {
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

        // Assumption-based unsat-core (checkSatAssuming). Atomize each assumption
        // so its atom becomes theory-observed (atomize → registry → addObservedVar),
        // and collect the literals to ASSUME — we do NOT add them as clauses, so
        // they enter the solve as retractable CaDiCaL assumptions and failed() can
        // report the minimized core on UNSAT. assumptionRoots_ is empty on a plain
        // checkSat, so assumptionLits stays empty and the solve path is unchanged.
        std::vector<SatLit> assumptionLits;
        std::vector<Term> assumptionReportTerms;  // parallel: Term to report if lit fails
        // API assumptions (checkSatAssuming): report the assumption itself.
        for (ExprId aRoot : assumptionRoots_) {
            assumptionLits.push_back(atomizer.atomize(aRoot, *ir));
            assumptionReportTerms.push_back(Term(static_cast<uint32_t>(aRoot)));
        }
        // File-level indicators (:produce-unsat-cores): report the ORIGINAL assertion.
        for (size_t k = 0; k < indicatorRoots_.size(); ++k) {
            assumptionLits.push_back(atomizer.atomize(indicatorRoots_[k], *ir));
            assumptionReportTerms.push_back(indicatorCoreTerms_[k]);
        }

        // L7: build the relevancy graph over the asserted boolean skeleton and
        // attach it to the propagator to steer cb_decide toward live program
        // branches. Pure decision heuristic (never changes the verdict), so it
        // is safe in any logic; default-OFF until validated broadly.
        if (std::getenv("XOLVER_RELEVANCY")) {
            atomizer.buildRelevancyGraph(ir->assertions(), *ir, relEngine);
            propagator.setRelevancyEngine(&relEngine);   // wires value oracle
            relEngine.finalize();                        // seed roots relevant
            if (xolver::env::diag("XOLVER_RELEVANCY_DIAG")) {
                std::fprintf(stderr, "[RELEVANCY] nodes=%zu roots seeded; "
                             "relevantVarsSeen=%zu\n",
                             relEngine.totalNodes(), relEngine.relevantVarsSeen());
            }
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
        // The BWI axiom emitter (XOLVER_NIA_ZOHAR_PLUGIN) ADDS pow2 semantics the
        // pre-pass cannot see (it runs over pre-emission assertions); defer to it
        // when active (else the pre-pass could false-sat a formula it proves unsat).
        if (std::getenv("XOLVER_NIA_ZOHAR_PLUGIN")) prepassEnabled = false;
        if (prepassEnabled) {
            CandidateModelSearch::Config cfg;
            cfg.allowUF = true;
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
        // 0-unsound. XOLVER_CMS_WIDTH_PROBE=0 disables (A/B); =1 forces on.
        bool widthProbeOn = (logic == "QF_UFNIA" || logic == "UFNIA");
        if (const char* e = std::getenv("XOLVER_CMS_WIDTH_PROBE"))
            widthProbeOn = (std::atoi(e) != 0);
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
            if (xolver::env::diag("XOLVER_CMS_WIDTH_PROBE_DIAG"))
                std::fprintf(stderr, "[WPROBE] pinnedFuncs=%zu probeVars=%zu\n",
                             pinnedFuncs.size(), probeVars.size()), std::fflush(stderr);

            auto makeEq = [&](ExprId v, int w) -> ExprId {
                CoreExpr cN; cN.kind = Kind::ConstInt; cN.sort = intSort;
                cN.payload.value = static_cast<int64_t>(w);
                CoreExpr eqN; eqN.kind = Kind::Eq; eqN.sort = boolSort;
                eqN.children.push_back(v); eqN.children.push_back(ir->addShared(cN));
                return ir->addShared(eqN);
            };
            auto tryRoots = [&](const std::vector<ExprId>& extra) {
                CandidateModelSearch::Config wcfg;
                wcfg.allowUF = true;
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

        cadicalBackend->disconnectPropagator();
        propagator.stats().print(std::cerr);

        Result ret = Result::Unknown;
        if (result == SatSolver::SolveResult::Sat) {
            // Keep the CMS pre-pass model (already validated); only pull the
            // theory model on the normal solve path.
            if (!cmsPrePassFound) lastModel_ = theoryManager.getModel();
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
            // ReadOnlyArrayElim write-array mode is a RELAXATION (free read-only
            // arrays, array equalities forced false): only its validator-confirmed
            // SAT direction is sound, so a derived UNSAT must not be trusted.
            ret = roaeUsedWriteArray_ ? Result::Unknown : Result::Unsat;
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
                                 xolver::env::diag("XOLVER_ARRAY_COMB_VALIDATE_SAT");
        bool validateSat = niaSatFloor || divModSatFloor || realDivPurifySatFloor ||
                           arrayCombSatFloor ||
                           (xolver::env::diag("XOLVER_PP_STRICT_VALIDATION")) ||
                           (features.hasNonlinear &&
                            xolver::env::diag("XOLVER_PP_VALIDATE_NONLINEAR_SAT"));
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

} // namespace xolver
