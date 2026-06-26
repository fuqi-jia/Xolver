#include "api/SolverImpl.h"

namespace xolver {

// Relocated Solver::Impl method definitions (declared in SolverImpl.h).

    // True iff the SMT-LIB input set :produce-models / issued (get-model).
bool Solver::Impl::modelRequestedImpl() const {
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
void Solver::Impl::mergeFixedBindings() {
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
bool Solver::Impl::modelViolatesOriginal() const {
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
bool Solver::Impl::arrayModelValidates() const {
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
bool Solver::Impl::arrayModelDefinitelyViolates() const {
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
        if (!roaeFreeArrayVars_.empty()) validator.setFreeArrayVars(&roaeFreeArrayVars_);
        validator.setNumericArrayElements(
            env::paramInt("XOLVER_COMB_ARRAY_BRIDGE_MODEL", 1) != 0);
        // XOLVER_DIAG_AM (diagnostic only): dump the array model + per-assertion
        // verdict so a floored array sat can be root-caused (which assertion,
        // which interp). Never affects the verdict.
        if (xolver::env::diag("XOLVER_DIAG_AM")) {
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
bool Solver::Impl::combinationModelDefinitelyViolates() const {
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
bool Solver::Impl::modelPositivelyValidates() const {
        if (!ir || !lastModel_) return false;
        const bool arrBridgeModel =
            env::paramInt("XOLVER_COMB_ARRAY_BRIDGE_MODEL", 1) != 0;
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
        for (const auto& [name, val] : lastModel_->assignments) {
            if (val.empty() || val[0] != '@') continue;
            // A genuinely-constrained combination scalar (e.g. a `ret` pinned by
            // `ret + 2^32 = (mod (sum of selects) 2^32)`) carries its REAL arith
            // value in numericAssignments; only the UNCONSTRAINED-scalar backfill
            // is spurious (minted 0, the alia_005 i=j collapse). With array-bridge
            // model completion on, keep the non-zero real value so a select/mod
            // equality over the scalar can validate; still drop the spurious
            // 0-collapse. Gated → default path unchanged.
            if (arrBridgeModel) {
                auto rit = lastModel_->numericAssignments.find(name);
                if (rit != lastModel_->numericAssignments.end()) {
                    auto q = rit->second.tryAsRational();
                    if (q && *q != 0) continue;  // real value → not opaque-excluded
                }
            }
            opaqueScalar.insert(name);
        }
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
        // --- Array-read bridge model back-fill -----------------------------
        // (XOLVER_COMB_ARRAY_BRIDGE_MODEL, default ON.)
        // The Purifier bridges each arithmetic array-read into a fresh shared
        // scalar via the assertion `(= v (select A idx))` (routed to EUF). The
        // arith theory assigns v a value, but EUF's array model does not
        // back-fill A[idx] with it, so the validator re-evaluates `(select A
        // idx)` to the array DEFAULT — a genuine sat whose witness flows through
        // a div/mod-over-array-read (the QF_ANIA UltimateAutomizer select-sum-mod
        // class) then fails to confirm and is floored to Unknown. UF apps do not
        // hit this: their bridge value lives in partialFuncModel_/functionInterps.
        // Complete the array interpretation from the bridges the solver already
        // satisfied: for each `(= v (select A idx))` with A a NAMED array
        // variable, set A[eval(idx)] = eval(v) in a local copy of the interps.
        // SOUND: the equality holds in the model (theory reported consistent), so
        // this only makes the array interp agree with a fact the model commits
        // to; the validator still independently re-checks every ORIGINAL
        // assertion, so a wrong model is never confirmed. Conflicting back-fills
        // (same index, different value) are skipped (conservative). Nested reads
        // `(select (select m b) i)` are left for the array operand resolves to a
        // non-variable — a follow-up (covers the 15 non-nested QF_ANIA today).
        // --- Array-read bridge model completion --------------------------
        // (XOLVER_COMB_ARRAY_BRIDGE_MODEL, default ON — PROMOTED 2026-06-05.
        //  Opt-out with =0. Promotion differential validated: combination reg
        //  alia/alra/auflia/auflra/ax + uflia/uflra/ufnia/ufnra = 0 verdict
        //  change / 0 unsound; NIA/NRA reg = 0 change (flag is scoped to "@"
        //  EUF-token scalars, untouched there); unit 1339/1339 flag-on; recovers
        //  +3 QF_ANIA select-sum-mod (sum10) from unknown→sat on the default path.
        //  The alra_010-class concern the master gated on does NOT materialize:
        //  the opaque-scalar real-value retention only KEEPS a genuinely-
        //  constrained non-zero value, never the spurious 0-collapse.)
        // The Purifier bridges each arithmetic array-read into a fresh shared
        // scalar via the assertion `(= v (select A idx))` (routed to EUF). The
        // arith theory assigns v a concrete value, but EUF's array-model export
        // does NOT reflect it, so the validator re-evaluates `(select A idx)` to a
        // stale default — a genuine sat whose witness flows through a
        // div/mod-over-array-read (the QF_ANIA UltimateAutomizer select-sum-mod
        // class) is then floored to Unknown. UF apps don't hit this: their value
        // lives in functionInterps. Surface each bridged read's value to the
        // validator KEYED BY THE SELECT NODE (ExprId): the value travels as a
        // typed RealValue (no string token round-trip) and the validator returns
        // it directly when it reaches that select term. SOUND: the bridge equality
        // holds in the model (theory reported consistent), and the validator still
        // independently re-checks every ORIGINAL assertion, so a globally
        // inconsistent value leaves the verdict Unknown — never a wrong sat.
        ArithModelValidator::SelectOverrideMap selBridge;
        if (arrBridgeModel) {  // declared at function top
            // Evaluate bridge indices with the FULL numeric channel: a compound
            // index may itself be a bridged shared scalar (opaque-token tagged,
            // hence excluded from numAsg as an opaqueScalar); its concrete value
            // lives in numericAssignments. Re-admit those here so index eval
            // matches what the validator computes for the ORIGINAL select's index.
            ArithModelValidator::NumAssignment numAsgFull = numAsg;
            for (const auto& [nm, rv2] : lastModel_->numericAssignments)
                if (auto q = rv2.tryAsRational()) numAsgFull[nm] = *q;
            ArithModelValidator idxEval(*ir, numAsgFull, boolAsg);
            for (ExprId aid : ir->assertions()) {
                const CoreExpr& a = ir->get(aid);
                if (a.kind != Kind::Eq || a.children.size() != 2) continue;
                ExprId selId = NullExpr, valId = NullExpr;
                for (int s = 0; s < 2; ++s) {
                    const CoreExpr& c = ir->get(a.children[s]);
                    if (c.kind == Kind::Select &&
                        (c.sort == ir->intSortId() || c.sort == ir->realSortId())) {
                        selId = a.children[s];
                        valId = a.children[1 - s];
                        break;
                    }
                }
                if (selId == NullExpr) continue;
                const CoreExpr& sel = ir->get(selId);
                if (sel.children.size() != 2) continue;
                // Key on (array-operand node, index value): robust to purification
                // rebuilding the bridge's select for a compound index, and to
                // nested reads (the inner array operand keeps its ExprId).
                auto idxV = idxEval.evalNumber(sel.children[1]);
                if (!idxV) continue;
                // The bridged value is the OTHER side of the equality — a fresh
                // shared scalar variable. Read its TYPED value from the theory's
                // numeric channel (the bridge var is also tagged with an EUF
                // identity token, so it is excluded from numAsg as an opaqueScalar
                // above; numericAssignments still carries its concrete value).
                const CoreExpr& valNode = ir->get(valId);
                if (valNode.kind != Kind::Variable) continue;
                const std::string* vn =
                    std::get_if<std::string>(&valNode.payload.value);
                if (!vn) continue;
                RealValue rv;
                auto rit = lastModel_->numericAssignments.find(*vn);
                if (rit != lastModel_->numericAssignments.end()) {
                    rv = rit->second;
                } else {
                    auto nit = numAsg.find(*vn);
                    if (nit == numAsg.end()) continue;
                    rv = RealValue::fromMpq(nit->second);
                }
                selBridge.emplace(std::make_pair(sel.children[0], *idxV), rv);  // first wins
            }
        }
        // --- ReadOnlyArrayElim (XOLVER_TARGETED_PP) read reconstruction ---
        // Each Ackermannized scalar read `(select arrOperand idxExpr)` -> fresh
        // var becomes a select override keyed (arrOperand-ExprId, value(idxExpr))
        // -> value(freshVar). The arrOperand/idxExpr ExprIds are hash-cons-stable
        // in the ORIGINAL snapshot, so the original array reads now evaluate
        // concretely. SOUND: every original assertion is still independently
        // re-checked here, so a wrong reconstructed value -> Violated/Indeterminate
        // -> NOT Satisfied -> Unknown (never a spurious sat).
        if (!roaeReads_.empty()) {
            ArithModelValidator::NumAssignment numAsgFull = numAsg;
            for (const auto& [nm, rv2] : lastModel_->numericAssignments)
                if (auto q = rv2.tryAsRational()) numAsgFull[nm] = *q;
            ArithModelValidator idxEval(*ir, numAsgFull, boolAsg);
            size_t roaeFound = 0, roaeDefault = 0, roaeNoIdx = 0;
            for (const auto& rr : roaeReads_) {
                auto idxV = idxEval.evalNumber(rr.idxExpr);
                if (!idxV) { ++roaeNoIdx; continue; }
                RealValue rv;
                auto rit = lastModel_->numericAssignments.find(rr.freshName);
                if (rit != lastModel_->numericAssignments.end()) {
                    rv = rit->second; ++roaeFound;
                } else {
                    auto nit = numAsg.find(rr.freshName);
                    if (nit != numAsg.end()) { rv = RealValue::fromMpq(nit->second); ++roaeFound; }
                    else { rv = RealValue::fromMpq(mpq_class(0)); ++roaeDefault; }
                }
                selBridge.emplace(std::make_pair(rr.arrOperand, *idxV), rv);  // first wins
            }
            if (xolver::env::diag("XOLVER_TARGETED_PP_DIAG"))
                std::fprintf(stderr, "[ROAE-RECON] reads=%zu found=%zu default0=%zu noIdx=%zu\n",
                             roaeReads_.size(), roaeFound, roaeDefault, roaeNoIdx);
        }
        // --- Datatype selector-bridge value back-fill (DT+arith combination) ---
        // Mirror of the array-read back-fill above: the Purifier bridges an
        // arith-valued datatype selector `(fst p)` via `(= v (fst p))` (routed to
        // EUF). The arith theory assigns v a concrete value, but the DT model
        // export does not reflect it, so the validator cannot evaluate `(fst p)`
        // and floors a genuine sat (e.g. `(* (fst p) (fst p)) = 16`) to Unknown.
        // Surface v's value keyed by the (hash-consed) selector ExprId. SOUND: the
        // bridge equality holds in the model and every ORIGINAL assertion is still
        // independently re-checked, so a globally-inconsistent value → Unknown.
        ArithModelValidator::SelectorOverrideMap selectorBridge;
        for (ExprId aid : ir->assertions()) {
            const CoreExpr& a = ir->get(aid);
            if (a.kind != Kind::Eq || a.children.size() != 2) continue;
            ExprId selId = NullExpr, valId = NullExpr;
            for (int s = 0; s < 2; ++s) {
                const CoreExpr& c = ir->get(a.children[s]);
                // Arith-valued datatype selector, or a UF application whose
                // argument may be a datatype value (funcInterps cannot key on a
                // DT arg) — both are EUF-owned reads the Purifier bridges.
                if ((c.kind == Kind::Selector || c.kind == Kind::UFApply) &&
                    (c.sort == ir->intSortId() || c.sort == ir->realSortId())) {
                    selId = a.children[s];
                    valId = a.children[1 - s];
                    break;
                }
            }
            if (selId == NullExpr) continue;
            const CoreExpr& valNode = ir->get(valId);
            if (valNode.kind != Kind::Variable) continue;
            const std::string* vn = std::get_if<std::string>(&valNode.payload.value);
            if (!vn) continue;
            auto rit = lastModel_->numericAssignments.find(*vn);
            if (rit != lastModel_->numericAssignments.end()) {
                selectorBridge.emplace(selId, rit->second);   // first wins
            } else {
                auto nit = numAsg.find(*vn);
                if (nit != numAsg.end())
                    selectorBridge.emplace(selId, RealValue::fromMpq(nit->second));
            }
        }

        // DT/UF selector value reconciliation across IR versions
        // (XOLVER_DT_SELECTOR_SEMANTIC_BRIDGE, default-ON). The override above keys on
        // the (purified) ir->assertions() selector ExprIds, but the validator
        // re-checks the ORIGINAL assertions, whose selector nodes can be DIFFERENT
        // ExprIds (purification rebuilt them). So a `(fst p)` inside a nonlinear term
        // (ufdtnia_001: (* (fst p) (fst p)) = 16) keeps the ORIGINAL node un-overridden
        // -> Indeterminate -> a genuine sat floors to Unknown. Reconcile by SEMANTIC
        // identity: build (selectorName, baseVarName) -> value from every bridge-shaped
        // equality (selector = model-valued var | int constant) over ALL assertions,
        // then key the override by the ORIGINAL selector node ExprIds the validator
        // actually evaluates. SOUND + additive: the value is theory-consistent and the
        // validator still independently re-checks every original assertion, so a wrong
        // value -> Violated/Indeterminate, never a confirmed false sat. Variable-base
        // selectors only; nested-base selectors stay Indeterminate (sound).
        static const bool dtSemBridge =
            xolver::env::flag("XOLVER_DT_SELECTOR_SEMANTIC_BRIDGE", true);
        if (dtSemBridge) {
            // Semantic identity of an EUF-owned arith read whose value the DT/EUF
            // model does not export: a datatype selector `(fst p)` -> "S\x01fst\x01p",
            // or a UF application over (datatype) variables `(f p)` -> "U\x01f\x01p".
            // Returns nullopt for non-Variable bases/args (kept Indeterminate = sound).
            auto semKey = [&](ExprId id) -> std::optional<std::string> {
                const CoreExpr& n = ir->get(id);
                if (n.kind == Kind::Selector && n.children.size() == 1) {
                    const std::string* fn = std::get_if<std::string>(&n.payload.value);
                    const CoreExpr& base = ir->get(n.children[0]);
                    const std::string* bn = base.kind == Kind::Variable
                        ? std::get_if<std::string>(&base.payload.value) : nullptr;
                    if (fn && bn) return "S\x01" + *fn + "\x01" + *bn;
                } else if (n.kind == Kind::UFApply) {
                    const std::string* fn = std::get_if<std::string>(&n.payload.value);
                    if (!fn) return std::nullopt;
                    std::string k = "U\x01" + *fn;
                    for (ExprId c : n.children) {
                        const CoreExpr& cn = ir->get(c);
                        if (cn.kind != Kind::Variable) return std::nullopt;  // all-Variable args only
                        const std::string* an = std::get_if<std::string>(&cn.payload.value);
                        if (!an) return std::nullopt;
                        k += "\x01" + *an;
                    }
                    return k;
                }
                return std::nullopt;
            };
            auto modelValueOf = [&](ExprId valId) -> std::optional<RealValue> {
                const CoreExpr& vnode = ir->get(valId);
                if (vnode.kind == Kind::Variable) {
                    if (const std::string* vn = std::get_if<std::string>(&vnode.payload.value)) {
                        auto rit = lastModel_->numericAssignments.find(*vn);
                        if (rit != lastModel_->numericAssignments.end()) return rit->second;
                        auto nit = numAsg.find(*vn);
                        if (nit != numAsg.end()) return RealValue::fromMpq(nit->second);
                    }
                } else if (vnode.kind == Kind::ConstInt) {
                    if (const int64_t* iv = std::get_if<int64_t>(&vnode.payload.value))
                        return RealValue::fromInt(*iv);
                }
                return std::nullopt;
            };
            // Pass 1: (semantic key) -> model value, from every bridge-shaped equality
            // `(= read value)` across ALL (purified) assertions.
            std::map<std::string, RealValue> semVal;
            for (ExprId aid : ir->assertions()) {
                const CoreExpr& a = ir->get(aid);
                if (a.kind != Kind::Eq || a.children.size() != 2) continue;
                for (int s = 0; s < 2; ++s) {
                    auto key = semKey(a.children[s]);
                    if (!key) continue;
                    if (auto v = modelValueOf(a.children[1 - s])) { semVal.emplace(*key, *v); break; }
                }
            }
            // Pass 2: key the ExprId-based override by the ORIGINAL read nodes the
            // validator actually evaluates (reconciling purified vs original node ids).
            if (!semVal.empty()) {
                std::unordered_set<ExprId> seen;
                std::function<void(ExprId)> scan = [&](ExprId e) {
                    if (e == NullExpr || !seen.insert(e).second) return;
                    const CoreExpr& n = ir->get(e);
                    if (n.kind == Kind::Selector || n.kind == Kind::UFApply) {
                        if (auto key = semKey(e)) {
                            auto it = semVal.find(*key);
                            if (it != semVal.end()) selectorBridge.emplace(e, it->second);  // first wins
                        }
                    }
                    for (ExprId c : n.children) scan(c);
                };
                for (ExprId aid : originalAssertions_) scan(aid);
            }
        }
        // #41 promoted default-ON: validator eval memoization is verdict-identical
        // (memoizes a PURE eval over ExprId) — a speedup on validator-heavy sat
        // re-checks, never changes a verdict. XOLVER_PP_VALIDATOR_MEMO=0 disables.
        const bool validatorMemo = xolver::env::flag("XOLVER_PP_VALIDATOR_MEMO", true);
        ArithModelValidator::Verdict v;
        if (!lastModel_->arrayInterps.empty() || !selBridge.empty() || !roaeFreeArrayVars_.empty()) {
            ArithModelValidator validator(*ir, numAsg, boolAsg,
                                          lastModel_->arrayInterps, tokAsg);
            validator.setFunctionInterps(&lastModel_->functionInterps);
            validator.setRealAssignments(&filteredReal);
            validator.setNumericArrayElements(arrBridgeModel);
            if (!selBridge.empty()) validator.setSelectOverride(&selBridge);
            if (!selectorBridge.empty()) validator.setSelectorOverride(&selectorBridge);
            if (!roaeFreeArrayVars_.empty()) validator.setFreeArrayVars(&roaeFreeArrayVars_);
            validator.setEvalMemo(validatorMemo);
            v = validator.validate(originalAssertions_);
        } else {
            ArithModelValidator validator(*ir, numAsg, boolAsg);
            validator.setFunctionInterps(&lastModel_->functionInterps);
            validator.setRealAssignments(&filteredReal);
            if (!selectorBridge.empty()) validator.setSelectorOverride(&selectorBridge);
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
void Solver::Impl::buildPartialFuncModel() {
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
bool Solver::Impl::realDivisionByZeroUnderModel(const ArithModelValidator& v) const {
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
    // True iff the ORIGINAL assertions syntactically contain a real `/`. The
    // realDivPurifySatFloor (which re-validates every nonlinear-real sat via the
    // RealValue ArithModelValidator) only guards the div-by-0 functional-consistency
    // corner of real division — with no real `/`, that corner cannot exist, so the
    // floor is pure overhead AND, for an algebraic (Q(sqrt c)) sat model, its
    // >=2-algebraic RealValue evaluation of a high-degree polynomial can blow up (the
    // Geogebra 17a/17b hang). Gating the floor on actual real division keeps the
    // soundness guard where it is needed and lets the algebraic-sat cascade through.
    // Memoized DAG walk.
bool Solver::Impl::hasRealDivisionInOriginal() const {
        if (!ir) return false;
        std::unordered_map<ExprId, bool> seen;
        std::function<bool(ExprId)> walk = [&](ExprId e) -> bool {
            if (e == NullExpr || e >= ir->size()) return false;
            if (!seen.emplace(e, true).second) return false;
            const CoreExpr& n = ir->get(e);
            if (n.kind == Kind::Div && ir->sortKind(n.sort) == SortKind::Real) return true;
            for (ExprId c : n.children) if (walk(c)) return true;
            return false;
        };
        for (ExprId a : originalAssertions_) if (walk(a)) return true;
        return false;
}

} // namespace xolver
