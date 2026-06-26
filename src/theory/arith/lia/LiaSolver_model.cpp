#include "util/MpqUtils.h"
#include "theory/arith/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/arith/lia/GomoryCut.h"
#include "theory/arith/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include "theory/arith/nia/reasoners/DioReasoner.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

// NOTE: This translation unit was split out of LiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheorySolver::TheoryModel> LiaSolver::getModel() const {
    return buildModel(/*includeInternal=*/false);
}

// NiaSolver's embedded linear-decide needs the COMPLETE assignment — including
// the internal/aux variables (e.g. NIA's `__nlc_div_q_*` / `__nlc_mod_r_*`
// mod/div-lowering vars) that getModel() hides — so it can re-validate the model
// against NIA's normalized constraints (those constraints reference the aux
// vars; dropping them and defaulting to 0 breaks the equality linkage).
std::optional<TheorySolver::TheoryModel> LiaSolver::getModelWithInternal() const {
    return buildModel(/*includeInternal=*/true);
}

std::optional<TheorySolver::TheoryModel> LiaSolver::buildModel(bool includeInternal) const {
    auto isInternal = [](const std::string& name) {
        return name.size() >= 2 && name[0] == '_' && name[1] == '_';
    };
    // If a rounding repair produced the SAT verdict, the simplex β holds the
    // fractional relaxation, not the integer model — return the repaired point.
    if (repairModel_) {
        TheoryModel model;
        for (const auto& [name, val] : *repairModel_) {
            if (name.empty()) continue;
            if (!includeInternal && isInternal(name)) continue;
            model.assignments[name] = val.get_num().get_str();
            model.numericAssignments.insert({name, RealValue::fromMpq(val)});
        }
        if (model.assignments.empty()) return std::nullopt;
        return model;
    }
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;           // skip unnamed auxiliary vars
        if (!includeInternal && isInternal(name)) continue; // internal
        DeltaRational val = gs_.value(i);
        // For integer variables, value should be integral after check().
        // If delta component is non-zero, take the rational part (delta is infinitesimal).
        if (val.b == 0 && val.a.get_den() == 1) {
            model.assignments[name] = val.a.get_num().get_str();
        } else {
            model.assignments[name] = val.a.get_str();
        }
        model.numericAssignments.insert({name, RealValue::fromMpq(val.a)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

std::optional<TheorySolver::TheoryModel> LiaSolver::findIntegerModel(
    int nodeCap, std::optional<TheoryConflict>* outConflict) {
    // One Full check applies bounds + LP + integrality repair. A Consistent
    // verdict is an immediate integer model; a branch Lemma leaves gs_ at a
    // fractional LP solution we drive to a leaf ourselves.
    TheoryLemmaDatabase scratch;
    TheoryCheckResult r = check(scratch, TheoryEffort::Full);
    if (r.kind == TheoryCheckResult::Kind::Consistent)
        return getModelWithInternal();
    if (r.kind == TheoryCheckResult::Kind::Conflict) {
        // Root LP infeasible (Farkas) ⇒ the asserted atoms are jointly
        // infeasible. Surface it as a sound conflict over the caller's real
        // reason literals.
        if (outConflict && r.conflictOpt) *outConflict = std::move(r.conflictOpt);
        return std::nullopt;
    }
    if (r.kind != TheoryCheckResult::Kind::Lemma)
        return std::nullopt;             // Unknown
    int nodes = 0;
    return branchAndBound(nodeCap, nodes);
}

std::optional<TheorySolver::TheoryModel> LiaSolver::branchAndBound(int nodeCap, int& nodes) {
    if (++nodes > nodeCap) return std::nullopt;   // give up → Unknown (sound)
    if (gs_.check() == GeneralSimplex::Result::Unsat) return std::nullopt;

    // Integrality repair shortcut at this node (tighter LP than the root).
    repairModel_.reset();
    if (tryIntegralityRepair()) {
        auto m = getModelWithInternal();
        repairModel_.reset();
        if (m) return m;
    }

    // Most-fractional integer variable. Branch ONLY on NAMED integer vars
    // (original + NIA's "__nlc_*" lowering vars). The unnamed LHS-form slack
    // columns (e.g. the simplex var for "Σbridge") are integer-valued too, but
    // they are DETERMINED by the named vars — branching them walks a huge range
    // (they are unbounded sums) without progress. Once every named integer var
    // is integral, the slacks are automatically integral.
    int bv = -1;
    mpq_class bestFrac(0);
    mpq_class bvVal;
    for (int v : integerVars_) {
        if (manager_.getVarName(v).empty()) continue;     // unnamed slack/aux
        DeltaRational dv = gs_.value(v);
        if (dv.b == 0 && dv.a.get_den() == 1) continue;   // already integral
        mpq_class frac;
        if (dv.b != 0) {
            frac = mpq_class(1, 2);
        } else {
            mpz_class fl;
            mpz_fdiv_q(fl.get_mpz_t(), dv.a.get_num().get_mpz_t(),
                       dv.a.get_den().get_mpz_t());
            frac = dv.a - mpq_class(fl);
            if (frac < 0) frac = -frac;
        }
        if (frac > bestFrac) { bestFrac = frac; bv = v; bvVal = dv.a; }
    }
    if (bv == -1) {
        // Every integer var is integral. The point may still violate a
        // disequality; the embedded-decide caller re-validates against NIA's
        // normalized constraints (which include the Neq atoms), so returning it
        // here is sound — a diseq-violating point is rejected upstream.
        return getModelWithInternal();
    }

    mpz_class fl;
    mpz_fdiv_q(fl.get_mpz_t(), bvVal.get_num().get_mpz_t(),
               bvVal.get_den().get_mpz_t());
    mpz_class cl = fl + 1;   // bvVal is fractional ⇒ ceil = floor + 1

    // Round to NEAREST integer — the side the LP value actually sits on. The mod
    // quotients here carry tiny near-integer fractions (e.g. -1/2^32), so a
    // floor-first order dives into the wrong half (floor(-1/2^32) = -1) and the
    // two coupled quotients ping-pong. Nearest-first collapses each to its LP
    // value in one node.
    mpz_class nr = roundNearest(bvVal);
    mpz_class other = (nr == fl) ? cl : fl;

    auto tryBound = [&](bool lower, bool upper, const mpz_class& val) -> std::optional<TheoryModel> {
        gs_.push();
        bool ok = true;
        if (lower) ok = gs_.assertLower(bv, BoundInfo(BoundValue(DeltaRational(mpq_class(val))))) && ok;
        if (upper) ok = ok && gs_.assertUpper(bv, BoundInfo(BoundValue(DeltaRational(mpq_class(val)))));
        std::optional<TheoryModel> m;
        if (ok) m = branchAndBound(nodeCap, nodes);
        gs_.pop();
        return m;
    };
    // PIN nearest, then the other neighbour (fixes free/near-integer vars in one
    // node). Then the open half-spaces preserve completeness — toward nearest first.
    if (auto m = tryBound(true, true, nr)) return m;          // pin = nearest
    if (auto m = tryBound(true, true, other)) return m;       // pin = other neighbour
    if (nr == cl) {  // nearest is the ceil side
        if (auto m = tryBound(true, false, cl)) return m;     // bv >= ceil
        if (auto m = tryBound(false, true, fl)) return m;     // bv <= floor
    } else {
        if (auto m = tryBound(false, true, fl)) return m;     // bv <= floor
        if (auto m = tryBound(true, false, cl)) return m;     // bv >= ceil
    }

    return std::nullopt;
}

std::string LiaSolver::mpqToSmtLib(const mpq_class& q) {
    if (q.get_den() == 1) {
        return q.get_num().get_str();
    }
    return "(/ " + q.get_num().get_str() + " " + q.get_den().get_str() + ")";
}

std::string LiaSolver::relationToSmtLib(Relation rel) {
    switch (rel) {
        case Relation::Eq:  return "=";
        case Relation::Lt:  return "<";
        case Relation::Leq: return "<=";
        case Relation::Gt:  return ">";
        case Relation::Geq: return ">=";
        case Relation::Neq: return "distinct";
    }
    return "=";
}

std::string LiaSolver::linearFormToSmtLib(const LinearFormKey& form) {
    if (form.terms.empty()) return "0";
    if (form.terms.size() == 1) {
        const auto& [name, coeff] = form.terms[0];
        if (coeff == 1) return name;
        if (coeff == -1) return "(- " + name + ")";
        return "(* " + mpqToSmtLib(coeff) + " " + name + ")";
    }
    std::string s = "(+";
    for (const auto& [name, coeff] : form.terms) {
        if (coeff == 1) {
            s += " " + name;
        } else if (coeff == -1) {
            s += " (- " + name + ")";
        } else {
            s += " (* " + mpqToSmtLib(coeff) + " " + name + ")";
        }
    }
    s += ")";
    return s;
}

void LiaSolver::dumpState(const std::string& tag) const {
    const char* env = std::getenv("XOLVER_LIA_DUMP_DIR");
    if (!env || !*env) return;
    std::filesystem::path dir(env);
    if (!std::filesystem::exists(dir)) {
        std::filesystem::create_directories(dir);
    }

    int id = ++dumpCounter_;
    std::filesystem::path path = dir / ("lia_dump_" + std::to_string(id) + "_" + tag + ".smt2");
    std::ofstream ofs(path);
    if (!ofs) return;

    ofs << "(set-logic QF_LIA)\n";

    // Collect all variable names
    std::unordered_set<std::string> vars;
    for (const auto& a : activeAtoms_) {
        for (const auto& t : a.lhs.terms) vars.insert(t.first);
    }
    for (const auto& d : disequalities_) {
        for (const auto& t : d.lhs.terms) vars.insert(t.first);
    }
    for (const auto& ie : interfaceEqualities_) {
        (void)ie;
    }

    for (const auto& v : vars) {
        ofs << "(declare-fun " << v << " () Int)\n";
    }

    // Active atoms
    for (const auto& a : activeAtoms_) {
        Relation effectiveRel = a.value ? a.rel : negateRelation(a.rel);
        std::string lhsStr = linearFormToSmtLib(a.lhs);
        std::string rhsStr = mpqToSmtLib(a.rhs);
        if (effectiveRel == Relation::Neq) {
            ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
        } else {
            ofs << "(assert (" << relationToSmtLib(effectiveRel) << " " << lhsStr << " " << rhsStr << "))\n";
        }
    }

    // Disequalities
    for (const auto& d : disequalities_) {
        std::string lhsStr = linearFormToSmtLib(d.lhs);
        std::string rhsStr = mpqToSmtLib(d.rhs);
        ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
    }

    ofs << "(check-sat)\n";

    if (tag == "sat") {
        ofs << "(get-model)\n";
    }

    ofs.flush();
}

} // namespace xolver
