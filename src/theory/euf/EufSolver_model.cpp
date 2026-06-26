#include <cstdlib>
#include "util/EnvParam.h"
#include <chrono>
#include "theory/euf/EufSolver.h"
#include "util/SolveClock.h"
#include <stdexcept>
#include "theory/array/AniaProfile.h"
#include "theory/combination/CareGraph.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/datatype/DtModelValidator.h"
#include "expr/ir.h"
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

std::optional<TheorySolver::TheoryModel> EufSolver::getModel() const {
    // The array/scalar model must be read off the egraph WHILE it reflects the
    // satisfying assignment. By the time the Solver calls getModel() (after
    // solve() returns), the egraph has been rolled back, so select/bridge
    // merges no longer hold. We therefore return the snapshot captured at the
    // last consistent Full-effort check. Fall back to a live build only if no
    // snapshot exists (defensive — e.g. a non-array EUF problem).
    if (modelSnapshot_) return modelSnapshot_;
    return buildModel();
}

// Canonical class token in the ArithModelValidator's namespaced form so the
// validator's asToken() and these tokens compare identically:
//   numeric literal  -> "#n:<canonical-rational>"
//   bool literal      -> "#b:1" / "#b:0"
//   otherwise         -> opaque per-class marker "@e<rep>"
// Index/element sorts may be uninterpreted; equality-by-token is exactly the
// QF_AX semantics (and, for Track 3, the UF argument/value identity).
std::string EufSolver::classToken(EufTermId t) const {
    if (t == NullEufTerm) return "@nil";
    EClassId rep = egraph_.rep(t);
    for (EufTermId m : egraph_.classMembers(rep)) {
        const auto& mn = termManager_.node(m);
        if (mn.origin == NullExpr) continue;
        if (mn.origin == TrueSentinelExpr || mn.origin == FalseSentinelExpr) continue;
        const auto& e = coreIr_->get(mn.origin);
        if (e.isConst()) {
            if (auto* i = std::get_if<int64_t>(&e.payload.value))
                return "#n:" + mpq_class(*i).get_str();
            if (auto* b = std::get_if<bool>(&e.payload.value))
                return std::string("#b:") + (*b ? "1" : "0");
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                // Numeric literal stored as string (Int/Real const).
                try { return "#n:" + mpq_class(*s).get_str(); } catch (...) {}
                return *s;
            }
        }
    }
    return "@e" + std::to_string(rep);
}

std::string EufSolver::sortName(SortId s) const {
    auto sk = coreIr_->sortKind(s);
    if (sk == SortKind::Int) return "Int";
    if (sk == SortKind::Real) return "Real";
    if (sk == SortKind::Bool) return "Bool";
    return "U" + std::to_string(s);
}

std::optional<TheorySolver::TheoryModel> EufSolver::buildModel() const {
    if (!coreIr_) return std::nullopt;
    TheoryModel model;
    if (arrayMode_) buildArrayModel(model);
    // Track 3: token-keyed UF interps for combination model validation. Scoped
    // to combination (sharedTermRegistry_); pure QF_UF gets them from CMS.
    if (ufModelEnabled_ && sharedTermRegistry_) collectFunctionInterps(model);
    if (model.arrayInterps.empty() && model.functionInterps.empty() &&
        model.assignments.empty() && model.numericAssignments.empty())
        return std::nullopt;
    return model;
}

void EufSolver::tryEvaluateBuiltin(EufTermId t, int level) {
    if (!coreIr_) return;
    const auto& node = termManager_.node(t);
    if (node.args.empty()) return;

    std::string symName = termManager_.symbolName(node.symbol);
    if (symName.empty() || symName[0] != '#') return;

    // Collect constant argument values from the equivalence class of each arg.
    // Also record, per arg, the CONSTANT MEMBER term that supplied the value:
    // the merge "t = eval(args)" is justified by each arg being equal to that
    // constant (e.g. x+1 = 2 holds because x = 1). Capturing (arg, constMember)
    // lets explainEquality recurse into explain(arg ≡ constMember) and reach the
    // base literals — without it the BuiltinEval merge carried an empty reason,
    // producing an INCOMPLETE conflict explanation (false-UNSAT / stale-merge
    // dependency hidden from conflict analysis).
    std::vector<mpq_class> values;
    std::vector<std::pair<EufTermId, EufTermId>> argConstPairs;
    values.reserve(node.args.size());
    argConstPairs.reserve(node.args.size());
    for (EufTermId arg : node.args) {
        EClassId cid = egraph_.rep(arg);
        bool found = false;
        mpq_class val;
        EufTermId constMember = NullEufTerm;
        for (EufTermId member : egraph_.classMembers(cid)) {
            const auto& mnode = termManager_.node(member);
            if (mnode.origin == NullExpr) continue;
            const auto& expr = coreIr_->get(mnode.origin);
            if (!expr.isConst()) continue;
            if (auto* i = std::get_if<int64_t>(&expr.payload.value)) {
                val = mpq_class(*i);
                found = true;
                constMember = member;
                break;
            } else if (auto* s = std::get_if<std::string>(&expr.payload.value)) {
                try {
                    val = mpq_class(*s);
                    found = true;
                    constMember = member;
                    break;
                } catch (...) {
                    continue;
                }
            }
        }
        if (!found) return;
        values.push_back(val);
        argConstPairs.push_back({arg, constMember});
    }

    mpq_class result;
    bool ok = false;
    if (symName == "#builtin.Add") {
        if (values.size() != 2) return;
        result = values[0] + values[1];
        ok = true;
    } else if (symName == "#builtin.Sub") {
        if (values.size() != 2) return;
        result = values[0] - values[1];
        ok = true;
    } else if (symName == "#builtin.Neg") {
        if (values.size() != 1) return;
        result = -values[0];
        ok = true;
    } else if (symName == "#builtin.Mul") {
        if (values.size() != 2) return;
        result = values[0] * values[1];
        ok = true;
    } else if (symName == "#builtin.Div") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        result = values[0] / values[1];
        ok = true;
    } else if (symName == "#builtin.Mod") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        // mpq_class doesn't have mod; use integer mod if both are integers
        if (values[0].get_den() == 1 && values[1].get_den() == 1) {
            mpz_class r = values[0].get_num() % values[1].get_num();
            result = mpq_class(r);
            ok = true;
        }
    } else if (symName == "#builtin.Abs") {
        if (values.size() != 1) return;
        result = abs(values[0]);
        ok = true;
    }

    if (!ok) return;

    std::string resultStr = result.get_str();
    EufTermId constTerm = termManager_.internConstant(resultStr, node.sort);
    if (constTerm != NullEufTerm && !egraph_.same(t, constTerm)) {
        MergeReason mr;
        mr.kind = MergeReasonKind::BuiltinEval;
        mr.lit = SatLit();
        // Explanation = why each arg equals its constant. explainEquality folds a
        // non-AssertedEquality edge by recursing on argPairs, so populating them
        // makes the BuiltinEval merge's explanation complete (reaches the base
        // literals that fixed the args to constants).
        mr.argPairs = std::move(argConstPairs);
        // 2026-06-02 ROOT-CAUSE FIX for the UFE wrong-UNSAT class: tag the
        // PendingMerge with the CURRENT processing level — the BuiltinEval
        // fold is caused by a merge at `level`, so the resulting fold (and
        // any downstream congruences it triggers) must inherit `level` so
        // they get rolled back together. Pre-fix this push had the default
        // 0, which left BuiltinEval merges tagged level 0 and surviving any
        // backtrack — the source of stale Congruence edges on Wisa xs-10-08.
        PendingMerge pm{t, constTerm, mr};
        pm.level = level;
        mergeQueue_.push_back(pm);
    }
}

} // namespace xolver
