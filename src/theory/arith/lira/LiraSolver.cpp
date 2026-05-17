#include "theory/arith/lira/LiraSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "expr/ir.h"
#include <iostream>
#include <algorithm>

namespace nlcolver {

LiraSolver::LiraSolver() = default;
LiraSolver::~LiraSolver() = default;

void LiraSolver::push() {
    gsRelax_.push();
}

void LiraSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gsRelax_.pop();
    }
}

void LiraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void LiraSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
    gsRelax_.backtrackToLevel(level);
}

TheoryCheckResult LiraSolver::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort) {
    if (effort == TheoryEffort::Standard) {
        return checkStandardEffort(lemmaDb);
    }
    return checkFullEffort(lemmaDb);
}

TheoryCheckResult LiraSolver::checkStandardEffort(TheoryLemmaDatabase& /*lemmaDb*/) {
    gsRelax_.resetActiveBounds();
    disequalities_.clear();

    integerVars_.clear();
    for (const auto& a : activeAssignments_) {
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
        int auxVar = managerRelax_.getOrCreateAuxVar(gsRelax_, payload.lhs, payload.rhs);

        for (const auto& [name, coeff] : payload.lhs.terms) {
            (void)coeff;
            int v = managerRelax_.getOrCreateVar(gsRelax_, name);
            if (coreIr_) {
                // Try to determine sort from CoreIr by variable name
                for (size_t i = 0; i < coreIr_->size(); ++i) {
                    ExprId eid = static_cast<ExprId>(i);
                    const auto& expr = coreIr_->get(eid);
                    if (expr.kind == Kind::Variable) {
                        if (std::holds_alternative<std::string>(expr.payload.value)) {
                            if (std::get<std::string>(expr.payload.value) == name) {
                                if (expr.sort == coreIr_->intSortId()) {
                                    integerVars_.insert(v);
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }

        if (payload.rel == Relation::Neq) {
            disequalities_.push_back({auxVar, payload.lhs, payload.rhs, a.lit});
        } else {
            bool ok = managerRelax_.assertBound(gsRelax_, auxVar, payload.rel, a.value, a.lit, a.level);
            if (!ok) {
                return TheoryCheckResult::mkConflict(managerRelax_.translateConflict(gsRelax_));
            }
        }
    }

    auto res = gsRelax_.check();
    if (res == GeneralSimplex::Result::Unsat) {
        auto tc = TheoryConflict{};
        tc.clause = allActiveReasons();
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (res == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    if (isRelaxationIntegral() && validateFullModel()) {
        return TheoryCheckResult::consistent();
    }

    if (auto lemma = tryGenerateBranchLemma()) {
        return TheoryCheckResult::mkLemma(std::move(*lemma));
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult LiraSolver::checkFullEffort(TheoryLemmaDatabase& lemmaDb) {
    // V1: delegate to standard effort for now
    // TODO: implement InternalMilpEngine::checkComplete() path with diseq splitting
    return checkStandardEffort(lemmaDb);
}

bool LiraSolver::buildRelaxationBounds() {
    // Handled inline in checkStandardEffort
    return true;
}

bool LiraSolver::isRelaxationIntegral() const {
    for (int col : integerVars_) {
        auto val = gsRelax_.value(col);
        if (val.b != 0 || val.a.get_den() != 1) {
            return false;
        }
    }
    return true;
}

bool LiraSolver::validateFullModel() const {
    // Validate strict inequalities and disequalities
    for (const auto& d : disequalities_) {
        auto val = gsRelax_.value(d.auxVar);
        if (val.isZero()) {
            return false;
        }
    }
    return true;
}

std::optional<TheoryLemma> LiraSolver::tryGenerateBranchLemma() {
    // Find a fractional integer variable
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int col : integerVars_) {
        auto val = gsRelax_.value(col);
        if (val.b != 0 || val.a.get_den() != 1) {
            mpq_class frac;
            if (val.b != 0) {
                frac = mpq_class(1, 2);
            } else {
                mpz_class num = val.a.get_num();
                mpz_class den = val.a.get_den();
                mpz_class f = num / den;
                mpz_class r = num % den;
                mpz_class floorVal;
                if (r == 0) {
                    floorVal = f;
                } else if (num >= 0) {
                    floorVal = f;
                } else {
                    floorVal = f - 1;
                }
                frac = val.a - mpq_class(floorVal, 1);
                if (frac < 0) frac = -frac;
            }
            if (frac > bestFrac) {
                bestFrac = frac;
                bestVar = col;
            }
        }
    }

    if (bestVar == -1) return std::nullopt;

    int col = bestVar;
    auto val = gsRelax_.value(col);
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        if (val.b > 0) {
            floorVal = q;
            ceilVal = mpq_class(num + 1, 1);
        } else if (val.b < 0) {
            floorVal = mpq_class(num - 1, 1);
            ceilVal = q;
        } else {
            floorVal = q;
            ceilVal = q;
        }
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

    if (!registry_) return std::nullopt;

    std::string name = managerRelax_.getVarName(col);
    if (name.empty()) return std::nullopt;

    LinearFormKey form;
    form.terms.push_back({name, mpq_class(1)});

    auto litLo = registry_->getOrCreateLinearBoundAtom(form, Relation::Leq, floorVal, TheoryId::LIRA);
    auto litHi = registry_->getOrCreateLinearBoundAtom(form, Relation::Geq, ceilVal, TheoryId::LIRA);

    return TheoryLemma{{litLo, litHi}};
}

void LiraSolver::reset() {
    activeAssignments_.clear();
    disequalities_.clear();
    coreVarToLiraVar_.clear();
    liraVarToCoreVar_.clear();
    liraVarSort_.clear();
    liraVarToSimplexColRelax_.clear();
    gsRelax_.reset();
    gsReconstruct_.reset();
}

void LiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

void LiraSolver::setCoreIr(const CoreIr* ir) {
    coreIr_ = ir;
}

std::optional<TheorySolver::TheoryModel> LiraSolver::getModel() const {
    TheoryModel model;
    for (int i = 0; i < gsRelax_.numVars(); ++i) {
        std::string name = managerRelax_.getVarName(i);
        if (name.empty()) continue;
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;
        DeltaRational val = gsRelax_.value(i);
        if (val.b == 0 && val.a.get_den() == 1) {
            model.assignments[name] = val.a.get_num().get_str();
        } else {
            model.assignments[name] = val.a.get_str();
        }
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

std::vector<SatLit> LiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : activeAssignments_) {
        reasons.push_back(a.lit);
    }
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), reasons.end());
    return reasons;
}

DeltaRational LiraSolver::getRelaxationValue(int liraVarId) const {
    int col = liraVarToSimplexColRelax_[liraVarId];
    return gsRelax_.value(col);
}

} // namespace nlcolver
