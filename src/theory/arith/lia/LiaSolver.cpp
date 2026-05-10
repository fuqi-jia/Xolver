#include "theory/arith/lia/LiaSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include <cassert>
#include <algorithm>

namespace nlcolver {

LiaSolver::LiaSolver() = default;

void LiaSolver::push() {
    gs_.push();
}

void LiaSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LiaSolver::reset() {
    activeAssignments_.clear();
    activeAtoms_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    gs_.resetActiveBounds();
    manager_.resetBoundReasons();
}

void LiaSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, reason, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, reason, atom, value});
}

void LiaSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
}

TheoryCheckResult LiaSolver::check(TheoryLemmaDatabase& lemmaDb) {
    // Rebuild all state from current active assignments.
    gs_.resetActiveBounds();
    manager_.resetBoundReasons();
    disequalities_.clear();
    activeAtoms_.clear();
    pendingConflict_.reset();
    integerVars_.clear();

    for (const auto& a : activeAssignments_) {
        const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
        int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, payload.rhs);

        for (const auto& [name, coeff] : payload.lhs.terms) {
            (void)coeff;
            int v = manager_.getOrCreateVar(gs_, name);
            integerVars_.insert(v);
        }

        if (payload.rel == Relation::Neq) {
            disequalities_.push_back({auxVar, payload.lhs, payload.rhs, a.lit});
        } else {
            bool ok = manager_.assertBound(gs_, auxVar, payload.rel, a.value, a.lit, a.level);
            if (!ok) {
                pendingConflict_ = PendingConflict{a.level, manager_.translateConflict(gs_)};
                break;
            }
        }

        activeAtoms_.push_back({a.atom.exprId, auxVar, payload.rel, a.value, payload.lhs, payload.rhs, a.lit});
    }

    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    }

    auto r = gs_.check();
    if (r == GeneralSimplex::Result::Unsat) {
        return TheoryCheckResult::mkConflict(manager_.translateConflict(gs_));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    if (!disequalities_.empty()) {
        auto dr = handleDisequalities(lemmaDb);
        if (dr.kind != TheoryCheckResult::Kind::Consistent) {
            return dr;
        }
    }

    auto ir = checkIntegrality(lemmaDb);
    if (ir.kind == TheoryCheckResult::Kind::Consistent) {
        std::vector<DiseqValidationInfo> diseqInfos;
        for (const auto& d : disequalities_) {
            diseqInfos.push_back({d.auxVar});
        }
        if (!validator_.validateLiaModel(activeAtoms_, diseqInfos, integerVars_, gs_)) {
            return TheoryCheckResult::unknown();
        }
        return TheoryCheckResult::consistent();
    }

    if (!activeAtoms_.empty()) {
        auto cr = integerReasoner_.run(activeAtoms_);
        if (cr) {
            if (cr->kind == TheoryCheckResult::Kind::Lemma && cr->lemmaOpt) {
                if (!lemmaDb.contains(*cr->lemmaOpt)) return *cr;
            } else {
                return *cr;
            }
        }
    }

    if (ir.kind == TheoryCheckResult::Kind::Lemma && ir.lemmaOpt) {
        if (!lemmaDb.contains(*ir.lemmaOpt)) return ir;
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult LiaSolver::handleDisequalities(TheoryLemmaDatabase& /*lemmaDb*/) {
    for (const auto& d : disequalities_) {
        auto val = gs_.value(d.auxVar);
        if (!val.isZero()) {
            continue;
        }

        if (d.rhs.get_den() != 1) {
            continue;
        }

        mpz_class g = 0;
        for (const auto& t : d.lhs.terms) {
            const mpq_class& c = t.second;
            if (c.get_den() != 1) {
                g = 1;
                break;
            }
            mpz_class a = c.get_num();
            if (a < 0) a = -a;
            if (a == 0) continue;
            if (g == 0) {
                g = a;
            } else {
                mpz_class tmp;
                mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
                g = tmp;
            }
        }

        mpz_class c = d.rhs.get_num();

        if (g == 0) {
            if (c == 0) {
                return TheoryCheckResult::mkConflict(
                    TheoryConflict{{d.lit.negated()}});
            }
            continue;
        }

        if (c % g != 0) {
            continue;
        }

        assert(registry_ != nullptr);
        mpq_class leRhs = mpq_class(c - g, 1);
        mpq_class geRhs = mpq_class(c + g, 1);

        auto lit1 = registry_->getOrCreateLinearBoundAtom(d.lhs, Relation::Leq, leRhs, TheoryId::LIA);
        auto lit2 = registry_->getOrCreateLinearBoundAtom(d.lhs, Relation::Geq, geRhs, TheoryId::LIA);

        return TheoryCheckResult::mkLemma(
            TheoryLemma{{d.lit.negated(), lit1, lit2}});
    }
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LiaSolver::checkIntegrality(TheoryLemmaDatabase& /*lemmaDb*/) {
    for (int v : integerVars_) {
        auto val = gs_.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            assert(registry_ != nullptr);
            return TheoryCheckResult::mkLemma(buildBranchSplitLemma(v, val));
        }
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma LiaSolver::buildDiseqSplitLemma(const DiseqInfo& /*d*/) {
    return TheoryLemma{};
}

TheoryLemma LiaSolver::buildBranchSplitLemma(int var, const DeltaRational& val) {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        floorVal = q;
        ceilVal = q;
    } else {
        mpz_class f = num / den;
        mpz_class r = num % den;
        if (r == 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f, 1);
        } else if (num >= 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f + 1, 1);
        } else {
            floorVal = mpq_class(f - 1, 1);
            ceilVal = mpq_class(f, 1);
        }
    }

    std::string name = manager_.getVarName(var);
    if (name.empty()) {
        return TheoryLemma{};
    }

    LinearFormKey form;
    form.terms.push_back({name, mpq_class(1)});

    auto litLo = registry_->getOrCreateLinearBoundAtom(form, Relation::Leq, floorVal, TheoryId::LIA);
    auto litHi = registry_->getOrCreateLinearBoundAtom(form, Relation::Geq, ceilVal, TheoryId::LIA);

    return TheoryLemma{{litLo, litHi}};
}

} // namespace nlcolver
