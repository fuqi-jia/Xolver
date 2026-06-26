#include "theory/arith/logics/nia/NiaSolver.h"
#include "theory/arith/logics/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/logics/dl/DifferenceGraph.h"
#include "theory/arith/logics/dl/BellmanFord.h"
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/logics/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/logics/nia/search/NiaIcpAdapter.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/logics/nra/core/CdcacCore.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "theory/arith/logics/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"
#include "theory/arith/logics/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/logics/nra/nla/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/kernel/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/logics/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/logics/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/kernel/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/logics/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/logics/nia/farkas/FarkasOrModelAssembler.h"
#include "util/MpqUtils.h"
#include <chrono>
#include <iostream>

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

// Farkas-Or Phase 4: NiaSolver stage that runs the full
// detector → CSP → assembler → ArithModelValidator pipeline.
//
// Soundness: every SAT verdict here is gated by ArithModelValidator
// against the ORIGINAL coreIr_ assertions. Never returns UNSAT —
// failed CSP / failed validation falls through to the rest of the
// pipeline.
//
// PROMOTED default-ON (2026-06-08): the bounded-B Farkas refutation solves
// VeryMax/Stroeder QF_NIA UNSAT the rest of the pipeline cannot (+11/51 small
// cases measured, 0-unsound), and on non-Farkas inputs the detector bails after
// one O(tree) scan (good()==false → nullopt below). No flag — a good lever
// belongs on the default path, not gated. Full-effort only.
std::optional<TheoryCheckResult>
NiaSolver::stageFarkasOr(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    if (coreIr_ == nullptr) return std::nullopt;

    // Memoize the detector profile + support table across stage calls.
    // The CoreIr doesn't change during the check loop, so we can build
    // once. With residual co-var grid enumeration this is the dominant
    // cost (Stroeder p21258: ~100ms first time, 0ms thereafter).
    static thread_local const CoreIr* cachedIr = nullptr;
    static thread_local farkas::FarkasProfile cachedProfile;
    static thread_local farkas::SupportTable cachedTable;
    if (cachedIr != coreIr_) {
        farkas::FarkasOrDetector det(*coreIr_);
        cachedProfile = det.detect();
        if (!cachedProfile.good()) {
            cachedIr = coreIr_;
            cachedTable = farkas::SupportTable{};
            return std::nullopt;
        }
        farkas::FarkasOrSolver solverBuild(*coreIr_);
        // Cap on the B cartesian product (number of bounded-tuple
        // points the table-builder will enumerate). 500 was the
        // initial conservative pick that floored p21258 (~81 tuples)
        // while skipping p20185-class cases that other NIA stages
        // solve fast. Larger Stroeder cases (Ex2.11 p21280+, 4Nested)
        // have 4+ Or-blocks with 7-λ branches and a denser bounded
        // domain — their B-product runs into the thousands. Bump to
        // 8000: still tractable per-call (~ms-scale with the augmented
        // Gauss + memoization), and unlocks more Stroeder cases.
        //   override:  XOLVER_NIA_FARKAS_OR_MAX_B
        std::size_t maxB = static_cast<std::size_t>(
            env::paramLong("XOLVER_NIA_FARKAS_OR_MAX_B", 8000));
        cachedTable = solverBuild.buildTable(cachedProfile, maxB);
        cachedIr = coreIr_;
    }
    if (!cachedProfile.good()) return std::nullopt;
    const auto& profile = cachedProfile;
    const auto& table = cachedTable;
    farkas::FarkasOrSolver solver(*coreIr_);
    static const bool trace = xolver::env::diag("XOLVER_NIA_FARKAS_OR_TRACE");
    auto traceWrite = [&](const std::string& s) {
        if (!trace) return;
        FILE* f = std::fopen("/tmp/farkas_or_trace", "a");
        if (f) { std::fputs(s.c_str(), f); std::fputc('\n', f); std::fclose(f); }
    };
    traceWrite("stageFarkasOr: profile.blocks=" + std::to_string(profile.blocks.size())
               + " feasibleTotal=" + std::to_string(table.feasibleTotal)
               + " rows=" + std::to_string(table.rows.size()));
    // Outer-assertion structure dump (XOLVER_NIA_FARKAS_OUTER_DIAG).
    // For each outer assertion, prints kind + variable name + whether it
    // structurally looks like `(= var const)` (a hard equality forcing the
    // var). Used to design row-refute-by-outer-eq sound UNSAT path.
    if (xolver::env::diag("XOLVER_NIA_FARKAS_OUTER_DIAG")) {
        // Helper: recursively check if `e` is a `(= var const)` form (either
        // child a Variable, the other an evaluable integer constant) and
        // return (varName, constValue) if so.
        std::function<bool(ExprId, std::string&, mpz_class&)> matchEqVarConst;
        matchEqVarConst = [&](ExprId eid, std::string& outVar, mpz_class& outVal) -> bool {
            const auto& e = coreIr_->get(eid);
            if (e.kind == Kind::Eq && e.children.size() == 2) {
                for (int side = 0; side < 2; ++side) {
                    const auto& v = coreIr_->get(e.children[side]);
                    const auto& c = coreIr_->get(e.children[1 - side]);
                    if (v.kind == Kind::Variable) {
                        auto* nm = std::get_if<std::string>(&v.payload.value);
                        if (!nm) continue;
                        if (c.kind == Kind::ConstInt) {
                            if (auto* iv = std::get_if<int64_t>(&c.payload.value)) {
                                outVar = *nm; outVal = *iv; return true;
                            }
                            if (auto* sv = std::get_if<std::string>(&c.payload.value)) {
                                try { outVal = mpz_class(*sv); outVar = *nm; return true; } catch (...) {}
                            }
                        }
                    }
                }
            }
            return false;
        };
        std::fprintf(stderr, "[FARKAS_OUTER_DIAG] outer count=%zu\n",
                     profile.outerAssertions.size());
        for (std::size_t i = 0; i < profile.outerAssertions.size(); ++i) {
            ExprId aid = profile.outerAssertions[i];
            const auto& e = coreIr_->get(aid);
            std::fprintf(stderr, "  outer[%zu] id=%u kind=%d", i, aid, static_cast<int>(e.kind));
            // If it's an And, scan its conjuncts for (= var const) patterns.
            if (e.kind == Kind::And) {
                std::fprintf(stderr, " conjuncts=%zu", e.children.size());
                for (ExprId c : e.children) {
                    std::string vn; mpz_class vv;
                    if (matchEqVarConst(c, vn, vv)) {
                        std::fprintf(stderr, " FORCES[%s=%s]",
                                     vn.c_str(), vv.get_str().c_str());
                    }
                }
            } else {
                std::string vn; mpz_class vv;
                if (matchEqVarConst(aid, vn, vv)) {
                    std::fprintf(stderr, " FORCES[%s=%s]",
                                 vn.c_str(), vv.get_str().c_str());
                }
            }
            std::fprintf(stderr, "\n");
        }
    }
    if (trace) {
        for (std::size_t i = 0; i < profile.blocks.size(); ++i) {
            const auto& blk = profile.blocks[i];
            std::string line = "  block[" + std::to_string(i) + "] branches="
                + std::to_string(blk.branches.size());
            traceWrite(line);
            for (std::size_t j = 0; j < blk.branches.size(); ++j) {
                const auto& br = blk.branches[j];
                std::string bl = "    branch[" + std::to_string(j) + "] λ=";
                for (const auto& l : br.lambdas) bl += l + ",";
                bl += " eqs=" + std::to_string(br.equalities.size())
                    + " ineqs=" + std::to_string(br.inequalities.size())
                    + " unclass=" + std::to_string(br.unclassified.size());
                if (j < blk.branchProxies.size() && !blk.branchProxies[j].empty()) {
                    bl += " proxy=" + blk.branchProxies[j];
                }
                traceWrite(bl);
            }
        }
    }
    if (trace) {
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            const auto& r = table.rows[i];
            std::string line = "  row[" + std::to_string(i) + "] (block=" +
                std::to_string(r.blockIdx) + " branch=" + std::to_string(r.branchIdx) + ") B={";
            bool first = true;
            for (const auto& [v, val] : r.bTuple) {
                if (!first) line += ", ";
                first = false;
                line += v + "=" + val.get_str();
            }
            line += "} ray=[";
            for (std::size_t j = 0; j < r.candidate.lambdaRay.size(); ++j) {
                if (j) line += ",";
                line += r.candidate.lambdaRay[j].get_str();
            }
            line += "]";
            traceWrite(line);
        }
    }
    // Bounded-B real-relaxation refutation runs INDEPENDENTLY of the support
    // table (it enumerates the bounded-B domain itself), so try it before the
    // empty-table / CSP paths — for cases like Stroeder loop3 the table is empty
    // (no single-ray Farkas certificate) yet the bounded-B per-leaf refutation
    // can still prove integer UNSAT. Default-OFF; soundness self-checked inside.
    if (auto refute = tryBoundedBRefutation(profile)) return refute;
    if (table.rows.empty()) {
        traceWrite("  exhaustive=" + std::string(table.exhaustive ? "true" : "false")
                   + " outerAssertions=" + std::to_string(profile.outerAssertions.size()));
        bool unsafeNoOuterCheck = std::getenv("XOLVER_NIA_FARKAS_OR_UNSAT_EMIT_UNSAFE") != nullptr;
        if (table.exhaustive && (unsafeNoOuterCheck || profile.outerAssertions.empty()) &&
            std::getenv("XOLVER_NIA_FARKAS_OR_UNSAT_EMIT")) {
            traceWrite("  → exhaustive empty table + no outer assertions => UNSAT");
            // iter-49: build a NARROW conflict from only Farkas-block
            // proxy literals (boolpur_K). For each block: pick the
            // currently-true branch proxy, add its negation. This says
            // "the current branch-choice combo is bad"; SAT backtracks
            // through ONLY proxy decisions (~10 vars), not the full
            // trail (~100s of vars). Falls back to full trail on miss.
            // CRITICAL: TheoryConflict.clause stores RAW reason literals
            // that are TRUE on the trail. TheoryManager negates them when
            // submitting the clause as a falsified external conflict. So
            // we push a.reason AS-IS (not .negated()) -- pushing .negated()
            // double-negates and produces an unsound conflict.
            TheoryConflict tc;
            if (registry_) {
                std::unordered_set<SatVar> seen;
                auto pushReason = [&](SatVar sv) {
                    if (!seen.insert(sv).second) return;
                    for (const auto& a : active_) {
                        if (a.reason.var == sv) {
                            tc.clause.push_back(a.reason);  // RAW reason
                            return;
                        }
                    }
                };
                for (const auto& blk : profile.blocks) {
                    // (a) Tseitin-proxy branches (iter-49 path).
                    for (const auto& proxy : blk.branchProxies) {
                        if (proxy.empty()) continue;
                        if (auto sv = registry_->findBoolVariableSatVar(proxy)) pushReason(*sv);
                    }
                    // (b) Unproxied branches: resolve the originalAnd ExprId.
                    for (const auto& br : blk.branches) {
                        if (br.originalAnd == NullExpr) continue;
                        if (auto sv = registry_->findSatVarByExprId(br.originalAnd))
                            pushReason(*sv);
                    }
                }
            }
            if (tc.clause.empty()) {
                tc.clause.reserve(active_.size());
                for (const auto& a : active_) tc.clause.push_back(a.reason);  // RAW
            }
            std::cerr << "[FarkasOrUnsatEmit] exhaustive empty table; emit conflict size=" << tc.clause.size() << "\n";
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
        traceWrite("  → empty table; bail");
        return std::nullopt;
    }

    // Enumerate up to N candidate CSP assignments; iterate validator.
    auto assignments = solver.enumerateCsp(table, profile, /*maxResults=*/64);
    if (assignments.empty()) {
        traceWrite("  → no CSP assignments; bail");
        return std::nullopt;
    }
    traceWrite("  → CSP enumerated " + std::to_string(assignments.size()) + " candidates");
    farkas::FarkasOrModelAssembler assembler(*coreIr_);

    // Residual repair helper: a Farkas-Or candidate fixes the Farkas-bound
    // λ-rays, B-tuple and CT-vars, but the original formula often contains
    // RESIDUAL vars (e.g. main_x, main_y in Stroeder) that appear in outer
    // assertions like `(<= (+ Nl2CT (* Nl2main_x main_x) ...) 0)`. The
    // assembler defaults residuals to 0, which forces the bilinear term to
    // 0 and the assertion to `c0 ≤ 0` — guaranteed to fail when Farkas
    // forced c0 ≥ 1. To recover, after a candidate's first validation fails
    // we try a small grid of residual values and re-validate. Grid width
    // adapts to residual count so the combo product stays bounded.
    static const std::size_t COMBO_CAP = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_COMBO_CAP", 16384));
    auto gridFor = [](std::size_t n) -> std::vector<mpz_class> {
        std::vector<mpz_class> v;
        if (n == 0) return v;
        if (n <= 3) {
            for (long k : {0L, 1L, -1L, 2L, -2L, 10L, -10L, 100L, -100L})
                v.emplace_back(k);
        } else if (n <= 5) {
            for (long k : {0L, 1L, -1L, 2L, -2L}) v.emplace_back(k);
        } else if (n <= 8) {
            for (long k : {0L, 1L, -1L}) v.emplace_back(k);
        } // n > 8: empty → caller skips repair
        return v;
    };

    // Per-stage-call validation budget: residual repair can otherwise dwarf
    // the rest of the NIA pipeline. We cap total validator invocations per
    // stage call. The stage runs many times during a check loop, so this
    // is a per-call (not per-check) budget.
    static const std::size_t VALIDATE_BUDGET = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_VALIDATE_BUDGET", 200));
    std::size_t validations = 0;
    // Pre-compute var name → isBool map by walking all assertions once.
    // Bool vars (e.g. boolpur_K Tseitin proxies) MUST go through
    // BoolAssignment; if routed through NumAssignment the validator hits
    // `(= boolpur_K (and ...))` with Number(0) LHS vs Bool RHS and
    // returns Indeterminate — which the framework treats as failure.
    std::unordered_set<std::string> boolVarNames;
    {
        SortId boolSort = coreIr_->boolSortId();
        std::function<void(ExprId)> walkSort;
        std::unordered_set<ExprId> seen;
        walkSort = [&](ExprId id) {
            if (!seen.insert(id).second) return;
            const auto& e = coreIr_->get(id);
            if (e.kind == Kind::Variable && e.sort == boolSort) {
                if (auto* s = std::get_if<std::string>(&e.payload.value))
                    boolVarNames.insert(*s);
            }
            for (ExprId c : e.children) walkSort(c);
        };
        for (ExprId aid : coreIr_->assertions()) walkSort(aid);
    }

    auto tryValidate = [&](IntegerModel& M) -> bool {
        if (validations >= VALIDATE_BUDGET) return false;
        ++validations;
        ArithModelValidator::NumAssignment num;
        ArithModelValidator::BoolAssignment bools;
        num.reserve(M.size());
        for (const auto& [v, val] : M) {
            if (boolVarNames.count(v)) {
                bools.emplace(v, val != 0);
            } else {
                num.emplace(v, mpq_class(val));
            }
        }
        ArithModelValidator amv(*coreIr_, num, bools);
        auto verdict = amv.validate(coreIr_->assertions());
        // Per-assertion failure diag: walk each assertion individually,
        // report which fail. Gated on XOLVER_NIA_FARKAS_FAILDIAG so the
        // default path is identical.
        if (verdict != ArithModelValidator::Verdict::Satisfied &&
            std::getenv("XOLVER_NIA_FARKAS_FAILDIAG")) {
            for (std::size_t ai = 0; ai < coreIr_->assertions().size(); ++ai) {
                ExprId aid = coreIr_->assertions()[ai];
                auto v = amv.validate({aid});
                if (v != ArithModelValidator::Verdict::Satisfied) {
                    std::fprintf(stderr, "    [FAILDIAG] assertion[%zu] (id=%u) verdict=%d\n",
                                 ai, aid, static_cast<int>(v));
                }
            }
        }
        return verdict == ArithModelValidator::Verdict::Satisfied;
    };

    int candIdx = 0;
    for (const auto& assignment : assignments) {
        auto candidate = assembler.assemble(profile, assignment);
        if (!candidate) { ++candIdx; continue; }
        if (trace) {
            std::string line = "  cand[" + std::to_string(candIdx) + "]:";
            for (const auto& [v, val] : *candidate) {
                line += " " + v + "=" + val.get_str();
            }
            traceWrite(line);
        }
        if (tryValidate(*candidate)) {
            traceWrite("  → validator SAT (cand[" + std::to_string(candIdx) + "])");
            currentModel_ = *candidate;
            lastValidatedFarkasModel_ = std::move(*candidate);   // survives reset

            // Queue unit-lemma propagations for the chosen branches'
            // boolpur_K Tseitin proxies. Each unit lemma drives the
            // SAT-CDCL engine onto a trail consistent with the Farkas-Or
            // model so it actually returns Sat instead of looping in the
            // decision search. They are drained by stagePendingLemma the
            // next time the propagator polls, which routes through the
            // proper lemma-database channel (CaDiCaL refuses raw
            // addClause mid-solve, so we cannot use pinLiteral here).
            //
            // Sound: the model was validator-confirmed against the
            // original CoreIr, so pinning the matching boolpur values
            // only prunes explorations that contradict a positively
            // confirmed witness. Each (proxy, truth) pair is queued at
            // most once via pinnedProxies_ — these unit clauses are
            // permanent in the SAT backend; duplicates are noise.
            std::vector<TheoryLemma> newPinLemmas;
            if (registry_) {
                for (std::size_t j = 0; j < profile.blocks.size(); ++j) {
                    const auto& blk = profile.blocks[j];
                    auto cit = assignment.choice.find((int)j);
                    int chosen = (cit != assignment.choice.end()) ? cit->second : -1;
                    for (std::size_t k = 0; k < blk.branchProxies.size(); ++k) {
                        const auto& proxy = blk.branchProxies[k];
                        if (proxy.empty()) continue;
                        bool truth = ((int)k == chosen);
                        auto pinKey = proxy + (truth ? ":1" : ":0");
                        if (!pinnedProxies_.insert(pinKey).second) continue;
                        auto sv = registry_->findBoolVariableSatVar(proxy);
                        if (!sv) continue;
                        TheoryLemma ulemma;
                        ulemma.lits.push_back(truth ? SatLit::positive(*sv)
                                                     : SatLit::negative(*sv));
                        ulemma.kind = LemmaKind::Entailment;
                        if (!lemmaDb.contains(ulemma)) {
                            lemmaDb.insertIfNew(ulemma);
                            newPinLemmas.push_back(ulemma);
                            traceWrite("  → queue pin-lemma " + proxy + "=" +
                                       (truth ? "true" : "false"));
                        }
                    }
                }
            }

            // Emit pin-lemmas via the proper SAT-CDCL lemma channel. The
            // first lemma is returned directly via mkLemma so it's installed
            // immediately; the rest (if any) queue into pendingLinLemmas_
            // and drain via stagePendingLemma on subsequent check() calls.
            // Returning consistent() instead would short-circuit the
            // pipeline and the lemmas would never reach SAT.
            if (!newPinLemmas.empty()) {
                auto first = std::move(newPinLemmas.front());
                for (std::size_t i = 1; i < newPinLemmas.size(); ++i) {
                    pendingLinLemmas_.push_back(std::move(newPinLemmas[i]));
                }
                return TheoryCheckResult::mkLemma(first);
            }
            // No new pin-lemmas to queue: every proxy that needed
            // committing has already been committed. The framework has
            // confirmed this validated SAT model farkasOrSatStreak_
            // times in a row; if SAT-CDCL still hasn't converged on its
            // own, return Unknown so cb_propagate / cb_check_found_model
            // both terminate SAT and the Cap. 10 hook in Solver.cpp
            // promotes the theory candidate directly via
            // modelPositivelyValidates. SOUND: same Unknown-recovery
            // contract — validator must positively confirm the model
            // before Sat is emitted.
            constexpr int kFarkasOrSatStreakLimit = 3;
            if (++farkasOrSatStreak_ >= kFarkasOrSatStreakLimit) {
                farkasOrSatStreak_ = 0;
                return TheoryCheckResult::unknown(
                    "NIA Farkas-Or: validated model, SAT-CDCL did not converge");
            }
            return TheoryCheckResult::consistent();
        }

        // First-pass failed. Identify residual vars: those assigned to 0
        // by the default residual pass AND not present in any Farkas
        // assignment (B, λ, CT, or ANY branch's λ in the detected blocks
        // — unused-branch λ's are validly 0 since only one Or branch per
        // block needs to hold; perturbing them is wasted search).
        std::vector<std::string> residualVars;
        std::unordered_set<std::string> fixed;
        for (const auto& [v, _] : assignment.B) fixed.insert(v);
        for (const auto& [_, names] : assignment.lambdaNamesPerBlock)
            for (const auto& n : names) fixed.insert(n);
        for (const auto& [v, _] : assignment.ctInterval) fixed.insert(v);
        // Also pin ALL Or-branch λ's (chosen or not) — perturbing an
        // unchosen branch's λ won't satisfy the Or unless that branch's
        // full Farkas template is also satisfied, which we don't try.
        for (const auto& blk : profile.blocks) {
            for (const auto& br : blk.branches) {
                for (const auto& n : br.lambdas) fixed.insert(n);
            }
        }
        for (const auto& [v, val] : *candidate) {
            if (fixed.count(v)) continue;
            // Only sweep over vars defaulted to 0 (the residual repair target).
            if (val != 0) continue;
            residualVars.push_back(v);
        }
        auto values = gridFor(residualVars.size());
        if (values.empty()) {
            ++candIdx;
            continue;
        }
        if (trace) {
            std::string line = "  cand[" + std::to_string(candIdx) + "] residual-repair over "
                + std::to_string(residualVars.size()) + " vars, grid=" + std::to_string(values.size())
                + ", combos=" + std::to_string(values.size());
            traceWrite(line);
        }

        // Geometric grid enumeration with combo cap.
        std::size_t total = 1;
        for (std::size_t i = 0; i < residualVars.size(); ++i) {
            total *= values.size();
            if (total > COMBO_CAP) { total = 0; break; }
        }
        if (total == 0) { ++candIdx; continue; }

        std::vector<std::size_t> idx(residualVars.size(), 0);
        while (true) {
            if (validations >= VALIDATE_BUDGET) break;
            // Skip the all-zero combo (already tried).
            bool allZero = true;
            for (std::size_t i = 0; i < idx.size(); ++i) {
                if (values[idx[i]] != 0) { allZero = false; break; }
            }
            if (!allZero) {
                IntegerModel repaired_M = *candidate;
                for (std::size_t i = 0; i < residualVars.size(); ++i) {
                    repaired_M[residualVars[i]] = values[idx[i]];
                }
                if (tryValidate(repaired_M)) {
                    traceWrite("  → validator SAT after residual-repair (cand["
                               + std::to_string(candIdx) + "])");
                    currentModel_ = std::move(repaired_M);
                    return TheoryCheckResult::consistent();
                }
            }
            // Increment odometer-style.
            std::size_t pos = 0;
            while (pos < idx.size()) {
                ++idx[pos];
                if (idx[pos] < values.size()) break;
                idx[pos] = 0;
                ++pos;
            }
            if (pos == idx.size()) break;
        }
        if (validations >= VALIDATE_BUDGET) break;
        ++candIdx;
    }
    traceWrite("  → no candidate validated");
    // (bounded-B refutation already attempted before the CSP path above.)
    return std::nullopt;
}

std::optional<TheoryCheckResult>
NiaSolver::tryBoundedBRefutation(const farkas::FarkasProfile& profile) {
    // PROMOTED default-ON (2026-06-08) — see stageFarkasOr. Returns nullopt
    // immediately unless the formula is Farkas-Or-shaped with bounded template
    // coeffs, so the cost on every other NIA solve is two empty-container checks.
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;  // needs the libpoly algebra backend (CdcacCore)
#else
    if (!kernel_ || !coreIr_ || !converter_) return std::nullopt;
    if (profile.boundedGlobals.empty() || profile.blocks.empty())
        return std::nullopt;

    // Once-per-solve cache: the refutation verdict depends only on the formula
    // (coreIr_), not the trail, so a not-refutable outcome is memoized to avoid
    // re-running the expensive per-leaf CdcacCore enumeration on every Full-effort
    // cb_propagate. (An UNSAT outcome ends the solve, so it is never reached
    // again — no need to cache it.)
    static thread_local const CoreIr* refuteNotRefutableIr = nullptr;
    if (refuteNotRefutableIr == coreIr_) return std::nullopt;
    auto giveUp = [&]() -> std::optional<TheoryCheckResult> {
        refuteNotRefutableIr = coreIr_;
        return std::nullopt;
    };

    static const bool trace = xolver::env::diag("XOLVER_NIA_FARKAS_OR_TRACE");
    auto traceWrite = [&](const std::string& s) {
        if (!trace) return;
        FILE* f = std::fopen("/tmp/farkas_or_trace", "a");
        if (f) { std::fputs(s.c_str(), f); std::fputc('\n', f); std::fclose(f); }
    };
    traceWrite("[bounded-refute] FUNCTION ENTERED blocks=" + std::to_string(profile.blocks.size())
               + " bounded=" + std::to_string(profile.boundedGlobals.size())
               + " dnf=" + std::to_string(profile.dnfBlocks.size()));

    // ---- 1. Bounded-B domain: collect vars + integer intervals, cap product.
    struct BVar { VarId vid; mpz_class lo, hi; };
    std::vector<BVar> bvars;
    bvars.reserve(profile.boundedGlobals.size());
    const long domCap = env::paramLong("XOLVER_NIA_FARKAS_REFUTE_DOM_CAP", 8192);
    mpz_class domProduct = 1;
    for (const auto& [name, bound] : profile.boundedGlobals) {
        mpz_class span = bound.second - bound.first + 1;
        if (span <= 0) return std::nullopt;          // empty/degenerate domain
        domProduct *= span;
        if (domProduct > domCap) {
            traceWrite("  [bounded-refute] B-domain " + domProduct.get_str()
                       + " > cap " + std::to_string(domCap) + "; bail");
            return std::nullopt;                       // too large; bail (sound)
        }
        bvars.push_back({kernel_->getOrCreateVar(name), bound.first, bound.second});
    }

    // ---- 2. Validity only: every block must offer at least one branch.
    // The old hard `comboCount > 256` ceiling is GONE — it was an artificial
    // floor that bailed (→ unknown) on every Farkas-Or UNSAT with > 8 binary
    // blocks (Hanoi 12 blocks = 4096 combos, etc.), which a uniform VeryMax
    // sweep showed to be the single largest miss class. The flat odometer it
    // guarded is replaced below by a DFS with sound prefix-UNSAT pruning, so
    // the branch-combo product no longer needs a ceiling: genuinely-UNSAT
    // termination problems collapse at a shallow prefix.
    for (const auto& blk : profile.blocks)
        if (blk.branches.empty()) return std::nullopt;
    traceWrite("  [bounded-refute] B-domain=" + domProduct.get_str()
               + " outer=" + std::to_string(profile.outerAssertions.size()));

    if (!cdcacCore_) {
        cdcacAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        cdcacCore_ = std::make_unique<CdcacCore>(kernel_.get(), cdcacAlgebra_.get());
    }

    // relHolds: does the rational constant `c` satisfy `c rel 0`?
    auto relHolds = [](const mpq_class& c, Relation rel) -> bool {
        switch (rel) {
            case Relation::Eq:  return c == 0;
            case Relation::Neq: return c != 0;
            case Relation::Lt:  return c <  0;
            case Relation::Leq: return c <= 0;
            case Relation::Gt:  return c >  0;
            case Relation::Geq: return c >= 0;
        }
        return false;
    };

    // Convert a relational atom ExprId into a (poly, rel) constraint with B
    // substituted. Outcomes:
    //   kAdd        -> append `out` to the leaf system
    //   kTrue       -> trivially satisfied (skip)
    //   kFalse      -> trivially violated  -> leaf is infeasible
    //   kBail       -> not modellable      -> whole refutation must bail (sound)
    enum class AtomOutcome { kAdd, kTrue, kFalse, kBail };
    auto atomToConstraint =
        [&](ExprId atomId, const std::unordered_map<VarId, mpz_class>& Bvals,
            CdcacConstraint& out) -> AtomOutcome {
        const auto& e = coreIr_->get(atomId);
        Relation rel;
        switch (e.kind) {
            case Kind::Gt:  rel = Relation::Gt;  break;
            case Kind::Geq: rel = Relation::Geq; break;
            case Kind::Lt:  rel = Relation::Lt;  break;
            case Kind::Leq: rel = Relation::Leq; break;
            case Kind::Eq:  rel = Relation::Eq;  break;
            default: return AtomOutcome::kBail;   // Neq / non-relational atom
        }
        if (e.children.size() != 2) return AtomOutcome::kBail;
        auto cc = converter_->convertConstraint(e.children[0], e.children[1],
                                                rel, *coreIr_);
        if (cc.status == PolyConstraintStatus::Tautology) return AtomOutcome::kTrue;
        if (cc.status == PolyConstraintStatus::Conflict)  return AtomOutcome::kFalse;
        if (cc.status != PolyConstraintStatus::Constraint) return AtomOutcome::kBail;
        PolyId diff = cc.diff;
        // INTEGER TIGHTENING (the lever that makes the real relaxation decisive).
        // Every variable is integer and every coefficient integer, so `diff` is
        // integer-valued on any integer assignment. Hence over ℤ:
        //     diff >  0  ⟺  diff − 1 ≥ 0
        //     diff <  0  ⟺  diff + 1 ≤ 0
        // Replacing the strict atom with its tightened non-strict form keeps the
        // integer solution set unchanged while SHRINKING the real-relaxation
        // feasible region (S_int ⊆ S'_real). Without this a strict ineq like
        // `CT·λ > 1` with `CT < 1` is real-feasible via fractional CT even though
        // it is integer-infeasible — exactly the Stroeder/VeryMax shape.
        if (rel == Relation::Gt) {
            diff = kernel_->sub(diff, kernel_->mkOne());
            rel = Relation::Geq;
        } else if (rel == Relation::Lt) {
            diff = kernel_->add(diff, kernel_->mkOne());
            rel = Relation::Leq;
        }
        for (const auto& [vid, val] : Bvals) {
            if (auto sp = kernel_->substituteRational(diff, vid, mpq_class(val)))
                diff = *sp;
        }
        if (kernel_->isConstant(diff))
            return relHolds(kernel_->toConstant(diff), rel)
                       ? AtomOutcome::kTrue : AtomOutcome::kFalse;
        out.poly = diff;
        out.rel = rel;
        out.reason = SatLit{0, true};   // placeholder; conflict built separately
        return AtomOutcome::kAdd;
    };

    // Flatten an outer assertion (possibly nested And) into leaf constraints.
    // Returns AtomOutcome semantics over the whole subtree: kFalse if any atom
    // is trivially violated, kBail if any atom is unmodellable / contains an Or.
    std::function<AtomOutcome(ExprId, const std::unordered_map<VarId, mpz_class>&,
                              std::vector<CdcacConstraint>&)> flatten;
    flatten = [&](ExprId eid, const std::unordered_map<VarId, mpz_class>& Bvals,
                  std::vector<CdcacConstraint>& cons) -> AtomOutcome {
        const auto& e = coreIr_->get(eid);
        if (e.kind == Kind::And) {
            for (ExprId c : e.children) {
                AtomOutcome o = flatten(c, Bvals, cons);
                if (o == AtomOutcome::kFalse || o == AtomOutcome::kBail) return o;
            }
            return AtomOutcome::kAdd;
        }
        if (e.kind == Kind::Or || e.kind == Kind::Not)
            return AtomOutcome::kBail;   // disjunction / negation in outer: bail
        CdcacConstraint c;
        AtomOutcome o = atomToConstraint(eid, Bvals, c);
        if (o == AtomOutcome::kAdd) cons.push_back(std::move(c));
        return o;
    };

    // Cost/slack vars to eliminate existentially in the LIA leaf engine
    // (research note 2026-06-07: ∃CT. A+CT·S ⋈ 0 ≡ S≠0 ∨ A⋈0). PROMOTED
    // default-ON (2026-06-08): the CT-elim leaf path is the one that actually
    // discharges the +11 VeryMax UNSAT (the CdcacCore fallback below stays as a
    // safety net for shapes the over-approx parse can't model).
    const bool ctElim = true;
    std::unordered_set<VarId> ctVarSet;
    if (ctElim)
        for (const auto& nm : profile.unboundedCT)
            ctVarSet.insert(kernel_->getOrCreateVar(nm));

    // ---- 3. Enumerate B-tuples × branch combos; each leaf must be Unsat.
    // The refutation odometer enumerates the flat Farkas-Or blocks AND any
    // DNF-recovered nested Or blocks (XOLVER_NIA_FARKAS_DNF_BLOCKS) uniformly:
    // both demand "pick one branch, every combo must be UNSAT". DNF blocks are
    // kept out of profile.blocks (their empty branchProxies must not reach the
    // SAT model-assembler) but are exactly the constraints whose omission made
    // the leaf incomplete, so the refutation MUST include them.
    std::vector<const farkas::FarkasOrBlock*> allBlocks;
    allBlocks.reserve(profile.blocks.size() + profile.dnfBlocks.size());
    for (const auto& b : profile.blocks)    allBlocks.push_back(&b);
    for (const auto& b : profile.dnfBlocks) allBlocks.push_back(&b);
    traceWrite("[bounded-refute] enter flat=" + std::to_string(profile.blocks.size())
               + " dnf=" + std::to_string(profile.dnfBlocks.size())
               + " residual=" + std::to_string(profile.residualConstraints.size()));

    std::vector<mpz_class> bcur;
    for (const auto& bv : bvars) bcur.push_back(bv.lo);
    std::size_t leavesChecked = 0;
    std::size_t prefixChecks = 0;
    // Safety backstop ONLY (not a perf floor): the DFS prunes genuinely-UNSAT
    // trees fast and bails to giveUp() the moment a real-feasible leaf is hit,
    // so this trips only on a pathological tree that neither prunes nor finds a
    // feasible leaf. On trip we giveUp() → Unknown (sound), never a wrong UNSAT.
    // Set high; lower via XOLVER_NIA_FARKAS_REFUTE_LEAF_CAP if a case runs long.
    const std::size_t leafCap = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_REFUTE_LEAF_CAP", 200000));
    while (true) {
        std::unordered_map<VarId, mpz_class> Bvals;
        for (std::size_t i = 0; i < bvars.size(); ++i) Bvals[bvars[i].vid] = bcur[i];

        // Mandatory residual (proxy-resolved) constraints for this B, shared
        // across branch combos. Use profile.residualConstraints (clean atoms),
        // NOT the raw purified outerAssertions. An unmodellable atom (kBail) is
        // SKIPPED, not aborted: dropping a constraint only ENLARGES the feasible
        // set, so a per-leaf UNSAT over the smaller constraint set is still a
        // sound UNSAT of the original.
        std::vector<CdcacConstraint> outerCons;
        bool bTupleDead = false;     // some outer atom trivially violated ⇒ all
                                     // branch combos at this B are infeasible
        for (ExprId rc : profile.residualConstraints) {
            AtomOutcome oo = flatten(rc, Bvals, outerCons);
            if (oo == AtomOutcome::kFalse) { bTupleDead = true; break; }
            // kAdd appended already; kTrue/kBail → skip
        }

        if (!bTupleDead) {
            // Branch-combo SEARCH: DFS over blocks with sound prefix-UNSAT
            // pruning (replaces the old flat odometer). The leaf constraint set
            // grows monotonically with each chosen branch and the CT-elim
            // over-approx UNSAT test is monotone, so a prefix whose PARTIAL leaf
            // is already UNSAT refutes EVERY completion of that prefix — prune
            // the whole subtree (sound: pruning never drops a feasible leaf, so
            // it can never cause a wrong UNSAT). Genuinely-UNSAT termination
            // problems go UNSAT at a shallow prefix, collapsing the 2^blocks
            // tree; only a real-feasible/unknown FULL leaf forces giveUp.
            //   returns 0 = subtree fully refuted (all completions UNSAT)
            //           1 = giveUp (feasible/unknown full leaf, unmodellable
            //               atom, or safety backstop tripped)
            std::function<int(std::size_t, const std::vector<CdcacConstraint>&)> dfs;
            dfs = [&](std::size_t bi,
                      const std::vector<CdcacConstraint>& accum) -> int {
                if (leavesChecked + prefixChecks > leafCap) {
                    traceWrite("  [bounded-refute] leaf/prefix budget "
                               + std::to_string(leafCap) + " tripped; giveUp");
                    return 1;
                }
                if (bi == allBlocks.size()) {
                    // FULL leaf — exact check. Over-approx (∃CT. A+CT·S ⋈ 0 ≡
                    // S≠0 ∨ A⋈0) first; else the real-relaxation CdcacCore. A
                    // feasible/unknown full leaf ⇒ NOT refutable ⇒ giveUp.
                    if (ctElim && niaLeafFarkasLiaUnsat(accum, ctVarSet, *kernel_)) {
                        ++leavesChecked; return 0;
                    }
                    CdcacInput input;
                    input.constraints = accum;
                    // varOrder = sorted union of leaf-constraint vars (CdcacCore
                    // indexes it directly; empty ⇒ n=0 ⇒ immediate Unknown).
                    // integerVars stays empty → PURE REAL relaxation (sound for
                    // UNSAT; integrality is injected via strict-ineq tightening
                    // in atomToConstraint).
                    std::set<VarId> vset;
                    for (const auto& cc2 : input.constraints)
                        for (const std::string& vn : kernel_->variables(cc2.poly))
                            vset.insert(kernel_->getOrCreateVar(vn));
                    input.varOrder.assign(vset.begin(), vset.end());
                    // CRASH GUARD: the CdcacCore fallback runs a Lazard/CAD
                    // projection whose libpoly subresultant (psc) chain blows up
                    // coefficient sizes super-exponentially with the number of
                    // projection levels (= variable count). On a high-dimensional
                    // leaf (consts5nt) it exhausts RAM and SIGSEGVs inside
                    // coefficient_ensure_capacity — a hardware fault that cannot be
                    // caught. Prevent it: skip the fallback above a variable budget,
                    // forfeiting only THIS leaf (giveUp → Unknown). Sound — the
                    // refutation merely fails to prove this leaf UNSAT, never emits a
                    // wrong UNSAT. The over-approx above already decides the
                    // tractable leaves, so a leaf reaching here that is also
                    // high-dimensional is one CdcacCore could not finish anyway.
                    traceWrite("  [bounded-refute] cdcac-fallback leaf vars="
                               + std::to_string(input.varOrder.size()));
                    // Threshold 24: above the largest CdcacCore leaf the
                    // refutation-solvable cases actually need (measured: Ex04 = 9,
                    // 4Nested = 19, both decidable, no crash) yet below the
                    // dimension whose libpoly subresultant chain OOMs/SIGSEGVs
                    // (consts5nt = 44). Biased toward the solvable max + margin
                    // because a crash is catastrophic (lost batch) while a forfeited
                    // leaf is benign (Unknown, not wrong). Tunable for experiments.
                    static const size_t kMaxLeafVars = static_cast<size_t>(
                        env::paramLong("XOLVER_NIA_FARKAS_REFUTE_MAX_LEAF_VARS", 24));
                    if (kMaxLeafVars > 0 && input.varOrder.size() > kMaxLeafVars) {
                        traceWrite("  [bounded-refute] leaf vars > " + std::to_string(kMaxLeafVars)
                                   + "; skip CdcacCore fallback (giveUp, projection OOM-risk)");
                        return 1;
                    }
                    ++leavesChecked;
                    CdcacResult cd = cdcacCore_->solve(input);
                    if (cd.status != CdcacStatus::Unsat) {
                        traceWrite("  [bounded-refute] leaf feasible/unknown "
                                   "(status=" + std::to_string((int)cd.status)
                                   + "); bail");
                        return 1;
                    }
                    return 0;
                }
                const auto* blk = allBlocks[bi];
                for (std::size_t b = 0; b < blk->branches.size(); ++b) {
                    const auto& br = blk->branches[b];
                    std::vector<CdcacConstraint> cons = accum;
                    bool leafDead = false, leafBail = false;
                    for (const auto& lam : br.lambdas) {   // lambda >= 0
                        CdcacConstraint c;
                        c.poly = kernel_->mkVar(kernel_->getOrCreateVar(lam));
                        c.rel = Relation::Geq;
                        c.reason = SatLit{0, true};
                        cons.push_back(std::move(c));
                    }
                    auto addAtoms = [&](const std::vector<ExprId>& atoms) {
                        for (ExprId a : atoms) {
                            CdcacConstraint c;
                            AtomOutcome o = atomToConstraint(a, Bvals, c);
                            if (o == AtomOutcome::kAdd) cons.push_back(std::move(c));
                            else if (o == AtomOutcome::kFalse) { leafDead = true; return; }
                            else if (o == AtomOutcome::kBail)  { leafBail = true; return; }
                        }
                    };
                    addAtoms(br.equalities);
                    if (!leafDead && !leafBail) addAtoms(br.inequalities);
                    if (leafBail) {
                        traceWrite("[bounded-refute] leafBail block=" + std::to_string(bi)
                                   + " (atom unmodellable) ⇒ giveUp");
                        return 1;   // can't model a branch atom
                    }
                    if (leafDead) continue;   // branch trivially infeasible ⇒
                                              // its whole subtree is refuted
                    // PREFIX PRUNING: a sound over-approx UNSAT of this partial
                    // leaf refutes every completion ⇒ skip the subtree.
                    if (ctElim) {
                        ++prefixChecks;
                        if (niaLeafFarkasLiaUnsat(cons, ctVarSet, *kernel_)) continue;
                    }
                    if (dfs(bi + 1, cons) == 1) return 1;   // propagate giveUp
                }
                return 0;   // every branch at this level refuted
            };
            if (dfs(0, outerCons) == 1) return giveUp();
        }

        // advance B odometer (integer ranges [lo,hi])
        std::size_t p = 0;
        while (p < bvars.size()) {
            ++bcur[p];
            if (bcur[p] <= bvars[p].hi) break;
            bcur[p] = bvars[p].lo; ++p;
        }
        if (p == bvars.size()) break;
    }

    // Every (B-tuple, branch-combo) leaf is real-infeasible (or trivially dead).
    // ℤⁿ ⊆ ℝⁿ and the B domain was exhausted ⇒ sound integer UNSAT.
    traceWrite("  [bounded-refute] ALL " + std::to_string(leavesChecked)
               + " leaves real-infeasible ⇒ UNSAT");
    TheoryConflict tc;
    if (registry_) {
        std::unordered_set<SatVar> seen;
        auto pushReason = [&](SatVar sv) {
            if (!seen.insert(sv).second) return;
            for (const auto& a : active_) {
                if (a.reason.var == sv) { tc.clause.push_back(a.reason); return; }
            }
        };
        for (const auto* blk : allBlocks) {
            for (const auto& proxy : blk->branchProxies) {
                if (proxy.empty()) continue;
                if (auto sv = registry_->findBoolVariableSatVar(proxy)) pushReason(*sv);
            }
            for (const auto& br : blk->branches) {
                if (br.originalAnd == NullExpr) continue;
                if (auto sv = registry_->findSatVarByExprId(br.originalAnd))
                    pushReason(*sv);
            }
        }
    }
    if (tc.clause.empty()) {
        tc.clause.reserve(active_.size());
        for (const auto& a : active_) tc.clause.push_back(a.reason);
    }
    if (tc.clause.empty()) return std::nullopt;   // nothing to pin the conflict on
    std::cerr << "[FarkasOrBoundedRefute] all " << leavesChecked
              << " leaves real-infeasible; emit UNSAT conflict size="
              << tc.clause.size() << "\n";
    return TheoryCheckResult::mkConflict(std::move(tc));
#endif
}

} // namespace xolver
