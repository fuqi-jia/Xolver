#include "base/RuntimeConfig.h"
#include <cstdlib>
#include "base/EnvParam.h"
#include <chrono>
#include "search/euf/EufSolver.h"
#include "search/euf/RollbackUnionFind.h"
#include "base/SolveClock.h"
#include <stdexcept>
#include "search/array/AniaProfile.h"
#include "search/combination/CareGraph.h"
#include "contracts/DebugTrace.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/datatype/DtModelValidator.h"
#include "ir/NativeTerms.h"
#include <cassert>
#include <algorithm>
#include <functional>
#include <climits>
#include <map>
#include <optional>
#include <tuple>

namespace xolver {

// NOTE: This translation unit was split out of EufSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

void EufSolver::ensureDtContext() {
    if (!dtMode_ || !nativeTerms_) return;
    if (!dtReasoner_.active()) {
        dtReasoner_.setContext(&termManager_, &egraph_, nativeTerms_, dtRegistry_);
    }
    dtReasoner_.setBoolConstants(trueTerm_, falseTerm_);
    // Combination logics (QF_UFDTNIA/LIA) carry a shared-term registry; pure
    // QF_UFDT does not. Drives the finite-DT N-O completeness floor.
    dtReasoner_.setCombinationMode(sharedTermRegistry_ != nullptr);
}

void EufSolver::ensureArrayContext() {
    if (!arrayMode_ || !nativeTerms_) return;
    if (!arrayReasoner_.active()) {
        arrayReasoner_.setContext(&termManager_, &egraph_, nativeTerms_, arrayRegistry_);
        // In combination logics the indices/elements are shared arith terms;
        // hand the reasoner the SharedTermRegistry so Row2 builds (i=j) as a
        // shared-equality atom. Null in pure QF_AX.
        arrayReasoner_.setSharedTermRegistry(sharedTermRegistry_);
    }
}

std::vector<SharedTermId> EufSolver::arrayIndexSharedTerms() const {
    std::unordered_set<SharedTermId> set;
    if (arrayMode_) arrayReasoner_.collectIndexSharedTerms(set);
    return std::vector<SharedTermId>(set.begin(), set.end());
}

std::vector<SharedTermId> EufSolver::arrayValueSharedTerms() const {
    std::unordered_set<SharedTermId> set;
    if (arrayMode_) arrayReasoner_.collectValueSharedTerms(set);
    return std::vector<SharedTermId>(set.begin(), set.end());
}

std::vector<ArrayReasoner::ArrayDiseq> EufSolver::activeArrayDiseqs() const {
    std::vector<ArrayReasoner::ArrayDiseq> out;
    if (!arrayMode_ || !nativeTerms_) return out;
    auto isArraySort = [&](EufTermId t) {
        if (t == NullEufTerm) return false;
        return nativeTerms_->arraySortParams(termManager_.node(t).sort).has_value();
    };
    // Direct array disequalities (a != b asserted locally).
    for (const auto& d : disequalities_) {
        if (isArraySort(d.lhs) && isArraySort(d.rhs)) {
            out.push_back({d.lhs, d.rhs});
        }
    }

    // A disequality  h(..p..) != h(..q..)  between two applications of the SAME
    // function symbol that differ in EXACTLY ONE argument position soundly
    // entails  arg_p != arg_q  at that position (if they were equal the apps
    // would be congruent, hence equal, contradicting the diseq). When that arg
    // is array-sorted we surface (arg_p, arg_q) so Extensionality splits on it
    // (array_incompleteness1: g(a)!=g(b) ==> a!=b ==> select(a,k)!=select(b,k)).
    //
    // The diseq may live LOCALLY (disequalities_) or, after purification in
    // combination, on the SHARED bus as a scalar  s1 != s2  with the egraph
    // holding s1 = h(..p..), s2 = h(..q..). Matching disequalities by egraph
    // CLASS (egraph_.same), not by literal endpoints, covers both — this is the
    // "shared-bus scalar-only gap" fix.
    //
    // SOUNDNESS: the Ext lemma this feeds (a=b OR select(a,k)!=select(b,k)) is a
    // tautology, so emitting it for any pair is sound regardless of whether the
    // diseq is truly entailed; the contrapositive only governs WHICH pairs are
    // worth splitting on (precision + termination), never the verdict. The Ext
    // site re-checks array-sortedness as a second guard.
    // Group application terms by (symbol, arity). Restrict to USER-declared
    // functions: skip ALL internal symbols (#array.*, #builtin.*, #dt.*, …).
    // Array builtins (select/store) have dedicated Row1/Row2/Ext reasoning;
    // piggybacking the contrapositive on synthesized internal selects over a
    // self-store class explodes Ext with fresh witness indices (alra_010).
    // A user UF over arrays (g:Array->Int) is the genuine external observer
    // whose result-diseq forces an array-arg diseq (array_incompleteness1).
    std::unordered_map<uint64_t, std::vector<EufTermId>> byKind;
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        const auto& n = termManager_.node(t);
        if (n.args.empty()) continue;
        if (termManager_.symbolName(n.symbol).rfind("#", 0) == 0) continue;
        uint64_t key = (static_cast<uint64_t>(n.symbol) << 8) | (n.args.size() & 0xff);
        byKind[key].push_back(t);
    }
    auto appsKnownDisequal = [&](EufTermId t1, EufTermId t2) -> bool {
        // SAT-observed predicates are merged with true/false. Opposite
        // Boolean values need no separately asserted disequality literal,
        // but they still require distinct array arguments for a model.
        if (trueTerm_ != NullEufTerm && falseTerm_ != NullEufTerm &&
            ((egraph_.same(t1, trueTerm_) && egraph_.same(t2, falseTerm_)) ||
             (egraph_.same(t2, trueTerm_) && egraph_.same(t1, falseTerm_))))
            return true;
        auto match = [&](const ActiveDisequality& d) {
            return (egraph_.same(t1, d.lhs) && egraph_.same(t2, d.rhs)) ||
                   (egraph_.same(t1, d.rhs) && egraph_.same(t2, d.lhs));
        };
        for (const auto& d : disequalities_)       if (match(d)) return true;
        for (const auto& d : sharedDisequalities_) if (match(d)) return true;
        return false;
    };
    std::unordered_set<uint64_t> emitted;
    for (auto& kv : byKind) {
        auto& apps = kv.second;
        for (size_t p = 0; p < apps.size(); ++p) {
            for (size_t q = p + 1; q < apps.size(); ++q) {
                EufTermId t1 = apps[p], t2 = apps[q];
                // Trigger only on SCALAR-result user applications (e.g.
                // g:Array->Int). A user UF returning an ARRAY (h:X->Array) being
                // disequal is itself array-level — handled by the direct
                // array-diseq scan above — so skip it here to avoid redundant
                // Ext fan-out.
                if (isArraySort(t1)) continue;
                if (egraph_.same(t1, t2)) continue;
                if (!appsKnownDisequal(t1, t2)) continue;
                const auto& a1 = termManager_.node(t1).args;
                const auto& a2 = termManager_.node(t2).args;
                if (a1.size() != a2.size()) continue;
                int diffPos = -1;
                bool single = true;
                for (size_t i = 0; i < a1.size(); ++i) {
                    if (egraph_.same(a1[i], a2[i])) continue;
                    if (diffPos != -1) { single = false; break; }
                    diffPos = static_cast<int>(i);
                }
                if (!single || diffPos == -1) continue;
                EufTermId pArg = a1[diffPos], qArg = a2[diffPos];
                if (!isArraySort(pArg) || !isArraySort(qArg)) continue;
                uint64_t lo = pArg < qArg ? pArg : qArg;
                uint64_t hi = pArg < qArg ? qArg : pArg;
                uint64_t dk = (lo << 32) | hi;
                if (!emitted.insert(dk).second) continue;
                out.push_back({pArg, qArg});
            }
        }
    }
    return out;
}

std::optional<TheoryLemma> EufSolver::sharedArrayDisequalityLemma(TheoryLemmaStorage& db) {
    if (!arrayMode_ || !arrayRegistry_ || !sharedTermRegistry_ || !nativeTerms_)
        return std::nullopt;
    // Extensionality creates EUF read disequalities. When their classes contain
    // arithmetic bridges, arithmetic must receive the same disequality: merely
    // giving the reads different EUF tokens does not constrain their numbers.
    struct SharedMember { SharedTermId shared; EufTermId term; SortId sort; };
    std::map<EClassId, std::vector<SharedMember>> members;
    for (auto id : sharedTermRegistry_->allSharedTerms()) {
        const auto* s = sharedTermRegistry_->get(id);
        if (!s) continue;
        const auto kind = nativeTerms_->sortKind(s->sort);
        if (kind != SortKind::Int && kind != SortKind::Real) continue;
        const auto t = termManager_.findTerm(s->nativeExpr);
        if (t != NullEufTerm && egraph_.rep(t) != NullEClass)
            members[egraph_.rep(t)].push_back({id, t, s->sort});
    }
    for (const auto& d : disequalities_) {
        auto left = members.find(egraph_.rep(d.lhs));
        auto right = members.find(egraph_.rep(d.rhs));
        if (left == members.end() || right == members.end()) continue;
        for (const auto& a : left->second) for (const auto& b : right->second) {
            if (a.sort != b.sort || a.shared == b.shared) continue;
            auto lhs = egraph_.explainEquality(a.term, d.lhs);
            auto rhs = egraph_.explainEquality(b.term, d.rhs);
            if (!lhs.ok || !rhs.ok) continue;
            TheoryLemma lemma;
            lemma.lits.push_back(d.reason.negated());
            for (auto lit : lhs.reasons) lemma.lits.push_back(lit.negated());
            for (auto lit : rhs.reasons) lemma.lits.push_back(lit.negated());
            lemma.lits.push_back(arrayRegistry_->getOrCreateSharedEqualityAtom(
                a.shared, b.shared).negated());
            if (normalizeTheoryClause(lemma.lits) && !db.contains(lemma)) return lemma;
        }
    }
    return std::nullopt;
}

void EufSolver::buildArrayModel(TheoryModel& model) const {
    if (!arrayMode_ || !nativeTerms_) return;

    // Group array variables by eclass so equal arrays share one interp.
    // Identify array variables in the NativeTerms (Variable nodes with array sort).
    struct ArrBuild {
        std::string defaultVal;
        bool hasConstDefault = false;
        std::string indexSort, elemSort;
        // index-token -> value-token, plus the index-class rep used for dedup.
        std::vector<std::pair<std::string, std::string>> entries;
        std::unordered_set<EClassId> seenIdxClass;
    };
    std::unordered_map<EClassId, ArrBuild> byClass;

    // Collect every array variable EufTermId.
    std::vector<std::pair<std::string, EufTermId>> arrayVars;
    for (ExprId id = 0; id < static_cast<ExprId>(nativeTerms_->size()); ++id) {
        const auto& e = nativeTerms_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (!nativeTerms_->arraySortParams(e.sort)) continue;
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        // Intern is monotonic; the term should already exist if it was used.
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<NativeTerms&>(*nativeTerms_));
        if (t == NullEufTerm) continue;
        arrayVars.push_back({std::get<std::string>(e.payload.value), t});
    }
    // Array values also occur directly as UF arguments/results, without an
    // array variable naming the class (for example f(store(a,i,v))).
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        if (!nativeTerms_->arraySortParams(termManager_.node(t).sort)) continue;
        EClassId rep = egraph_.rep(t);
        auto& ab = byClass[rep];
        const auto& tn = termManager_.node(t);
        if (auto params = nativeTerms_->arraySortParams(tn.sort)) {
            ab.indexSort = sortName(params->first);
            ab.elemSort = sortName(params->second);
        }
        // const default if the class contains a const-array.
        if (!ab.hasConstDefault) {
            for (EufTermId m : egraph_.classMembers(rep)) {
                if (arrayReasoner_.isConstArray(m)) {
                    const auto& cn = termManager_.node(m);
                    if (cn.args.size() == 1) {
                        ab.defaultVal = classToken(cn.args[0]);
                        ab.hasConstDefault = true;
                    }
                    break;
                }
            }
        }
    }

  {
    // Solve finite array cells across EVERY store equation in each e-class.
    // Choosing one store as a recursive generator loses constraints from the
    // other generators, and cannot propagate a result read back into its base.
    // At an observed index, a store connects result/base cells unless it writes
    // that index. Outside the finite index set, all store edges share defaults.
    // Distinct index classes describe a candidate arrangement; combination and
    // original-formula model validation still check its arithmetic realization.
    std::map<EClassId, EClassId> slots;
    RollbackUnionFind defaults;
    for (const auto& [rep, ab] : byClass) slots.emplace(rep, defaults.addNode());
    std::map<EClassId, EufTermId> indices;
    for (auto sel : arrayReasoner_.selectTerms()) {
        const auto& n = termManager_.node(sel);
        if (n.args.size() == 2) indices.emplace(egraph_.rep(n.args[1]), n.args[1]);
    }
    for (auto store : arrayReasoner_.storeTerms()) {
        const auto& n = termManager_.node(store);
        if (n.args.size() != 3) continue;
        indices.emplace(egraph_.rep(n.args[1]), n.args[1]);
        defaults.unite(slots.at(egraph_.rep(store)), slots.at(egraph_.rep(n.args[0])));
    }
    // A concrete literal is preferable to an unconstrained token. Differing
    // pinned tokens indicate an unsatisfied candidate arrangement, not a proof
    // of inconsistency; the independent model checker must still accept it.
    auto pin = [](std::map<EClassId, std::string>& values, EClassId cell,
                  const std::string& value) {
        auto [it, fresh] = values.emplace(cell, value);
        if (!fresh && !value.empty() && value[0] != '@' &&
            !it->second.empty() && it->second[0] == '@') it->second = value;
    };
    std::map<EClassId, std::string> defaultValues;
    for (const auto& [rep, slot] : slots) {
        const auto& ab = byClass.at(rep);
        if (ab.hasConstDefault) pin(defaultValues, defaults.find(slot), ab.defaultVal);
    }
    for (const auto& [rep, slot] : slots) {
        const auto component = defaults.find(slot);
        auto [it, fresh] = defaultValues.emplace(component, "@def" + std::to_string(rep));
        byClass.at(rep).defaultVal = it->second;
        byClass.at(rep).entries.clear();
    }
    for (const auto& [indexClass, indexTerm] : indices) {
        RollbackUnionFind cells;
        for (std::size_t i = 0; i < slots.size(); ++i) cells.addNode();
        for (auto store : arrayReasoner_.storeTerms()) {
            const auto& n = termManager_.node(store);
            if (n.args.size() != 3 || egraph_.rep(n.args[1]) == indexClass) continue;
            cells.unite(slots.at(egraph_.rep(store)), slots.at(egraph_.rep(n.args[0])));
        }
        std::map<EClassId, std::string> values;
        for (const auto& [rep, slot] : slots) {
            const auto& ab = byClass.at(rep);
            if (ab.hasConstDefault) pin(values, cells.find(slot), ab.defaultVal);
        }
        for (auto store : arrayReasoner_.storeTerms()) {
            const auto& n = termManager_.node(store);
            if (n.args.size() == 3 && egraph_.rep(n.args[1]) == indexClass)
                pin(values, cells.find(slots.at(egraph_.rep(store))), classToken(n.args[2]));
        }
        for (auto sel : arrayReasoner_.selectTerms()) {
            const auto& n = termManager_.node(sel);
            if (n.args.size() == 2 && egraph_.rep(n.args[1]) == indexClass)
                pin(values, cells.find(slots.at(egraph_.rep(n.args[0]))), classToken(sel));
        }
        for (const auto& [rep, slot] : slots) {
            auto it = values.find(cells.find(slot));
            if (it == values.end()) continue; // unconstrained cell uses the component default
            const auto params = nativeTerms_->arraySortParams(termManager_.node(rep).sort);
            if (!params || params->first != termManager_.node(indexTerm).sort) continue;
            byClass.at(rep).entries.emplace_back(classToken(indexTerm), it->second);
        }
    }
  }

    for (const auto& [rep, ab] : byClass) {
        TheoryModel::ArrayInterp ai;
        ai.indexSort = ab.indexSort;
        ai.elemSort = ab.elemSort;
        ai.defaultVal = ab.defaultVal;
        ai.entries = ab.entries;
        model.arrayValues[classToken(rep)] = std::move(ai);
    }

    // Emit one ArrayInterp per array variable (sharing the class build).
    for (const auto& [name, t] : arrayVars) {
        EClassId rep = egraph_.rep(t);
        auto it = byClass.find(rep);
        if (it == byClass.end()) continue;
        TheoryModel::ArrayInterp ai;
        ai.indexSort = it->second.indexSort;
        ai.elemSort = it->second.elemSort;
        ai.defaultVal = it->second.defaultVal;
        ai.entries = it->second.entries;
        model.arrayInterps[name] = std::move(ai);
    }

    if (model.arrayValues.empty()) return;

    // Scalar token assignments for every non-array, non-bool variable that the
    // egraph knows about (index/element vars). The validator needs these to
    // evaluate select/store; tokens are the same class tokens used in the
    // array interps, so they stay consistent. Bool vars stay in `assignments`
    // as "true"/"false"; numeric literals stay numeric.
    for (ExprId id = 0; id < static_cast<ExprId>(nativeTerms_->size()); ++id) {
        const auto& e = nativeTerms_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (nativeTerms_->arraySortParams(e.sort)) continue;  // arrays handled above
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        const std::string& name = std::get<std::string>(e.payload.value);
        if (model.assignments.count(name)) continue;
        // Only emit if the variable was actually interned (used in a term).
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<NativeTerms&>(*nativeTerms_));
        if (t == NullEufTerm) continue;
        auto sk = nativeTerms_->sortKind(e.sort);
        if (sk == SortKind::Bool) {
            // Resolve against the true/false classes if forced; else default.
            if (trueTerm_ != NullEufTerm && egraph_.same(t, trueTerm_))
                model.assignments[name] = "true";
            else if (falseTerm_ != NullEufTerm && egraph_.same(t, falseTerm_))
                model.assignments[name] = "false";
            continue;
        }
        model.assignments[name] = classToken(t);
    }
    if (config::read<config::ReadKind::Presence>("XOLVER_DIAG_AM")) {
        std::cerr << "[DIAG_AM] EUF scalar snapshot:";
        for (const auto& [name, token] : model.assignments)
            std::cerr << ' ' << name << '=' << token;
        std::cerr << '\n';
    }
}

void EufSolver::collectFunctionInterps(TheoryModel& model) const {
    if (!nativeTerms_) return;

    // One FuncInterp per uninterpreted function symbol, keyed on the argument
    // CLASS TOKENS (canonical "#n:.."/"#b:.."/"@e.." form). Congruence closure
    // guarantees the table is a genuine function: two applications whose args
    // lie in the same classes are themselves congruent (same class), so they
    // produce identical arg-token tuples AND identical value tokens. The only
    // way the post-remap table (TheoryManager::getModel) could become
    // inconsistent is two DISTINCT classes collapsing to one arith number; the
    // remap's @CONFLICT guard + the per-function consistency check there reject
    // that, so an unsound interp is dropped (-> validator Indeterminate -> floor)
    // rather than confirming a wrong model.
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        const auto& n = termManager_.node(t);
        if (n.args.empty()) continue;            // not an application
        if (n.origin == NullExpr) continue;
        const auto& oe = nativeTerms_->get(n.origin);
        if (oe.kind != Kind::UFApply) continue;  // only genuine UF applications
        if (!std::holds_alternative<std::string>(oe.payload.value)) continue;
        const std::string& fname = std::get<std::string>(oe.payload.value);

        auto& fi = model.functionInterps[fname];
        if (fi.argSorts.empty() && !n.args.empty()) {
            for (EufTermId a : n.args)
                fi.argSorts.push_back(sortName(termManager_.node(a).sort));
            fi.retSort = sortName(n.sort);
            // Empty default: a tuple absent from the table -> the validator's
            // UFApply lookup sees an empty value -> Indeterminate (sound floor),
            // never a guessed value. Every UFApply in the ground assertions was
            // interned, so the table is complete for what the validator evaluates.
            fi.deflt = "";
        }
        TheoryModel::FuncEntry entry;
        entry.args.reserve(n.args.size());
        for (EufTermId a : n.args) entry.args.push_back(classToken(a));
        entry.value = classToken(t);
        bool dup = false;
        for (const auto& ex : fi.entries)
            if (ex.args == entry.args) { dup = true; break; }
        if (!dup) fi.entries.push_back(std::move(entry));
    }

    if (model.functionInterps.empty()) return;

    // Emit scalar var -> class-token assignments for every interned, non-array,
    // non-bool variable the egraph knows (incl. purification vars that appear as
    // UF arguments). TheoryManager::getModel pairs these tokens with the arith
    // model's numeric value to remap the function-interp arg/value tokens to the
    // bare rationals the validator expects. (Same mechanism the array path uses.)
    for (ExprId id = 0; id < static_cast<ExprId>(nativeTerms_->size()); ++id) {
        const auto& e = nativeTerms_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (nativeTerms_->arraySortParams(e.sort)) continue;
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        const std::string& name = std::get<std::string>(e.payload.value);
        if (model.assignments.count(name)) continue;
        EufTermId t = termManager_.findTerm(id);
        if (t == NullEufTerm) continue;
        auto sk = nativeTerms_->sortKind(e.sort);
        if (sk == SortKind::Bool) {
            if (trueTerm_ != NullEufTerm && egraph_.same(t, trueTerm_))
                model.assignments[name] = "true";
            else if (falseTerm_ != NullEufTerm && egraph_.same(t, falseTerm_))
                model.assignments[name] = "false";
            continue;
        }
        model.assignments[name] = classToken(t);
    }
}

} // namespace xolver
