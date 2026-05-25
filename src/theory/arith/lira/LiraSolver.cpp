#include "theory/arith/lira/LiraSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "expr/ir.h"
#include <algorithm>

namespace nlcolver {

LiraSolver::LiraSolver() = default;
LiraSolver::~LiraSolver() = default;

void LiraSolver::onPush() {
    milpEngine_.push();
}

void LiraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        milpEngine_.pop();
    }
}

TheoryCheckResult LiraSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    if (effort == TheoryEffort::Standard) {
        return checkStandardEffort(lemmaDb);
    }
    return checkFullEffort(lemmaDb);
}

bool LiraSolver::isIntegerVar(const std::string& name) const {
    if (!coreIr_) return false;
    for (size_t i = 0; i < coreIr_->size(); ++i) {
        ExprId eid = static_cast<ExprId>(i);
        const auto& expr = coreIr_->get(eid);
        if (expr.kind == Kind::Variable) {
            if (std::holds_alternative<std::string>(expr.payload.value)) {
                if (std::get<std::string>(expr.payload.value) == name) {
                    return expr.sort == coreIr_->intSortId();
                }
            }
        }
    }
    return false;
}

TheoryCheckResult LiraSolver::checkStandardEffort(TheoryLemmaStorage& /*lemmaDb*/) {
    milpEngine_.clear();
    disequalities_.clear();
    std::unordered_map<std::string, int> nameToIdx;

    for (const auto& a : trail()) {
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);

        // Compute effective relation (handle negated literals)
        Relation effRel = p.rel;
        if (!a.value) {
            switch (p.rel) {
                case Relation::Eq:  effRel = Relation::Neq; break;
                case Relation::Neq: effRel = Relation::Eq; break;
                case Relation::Lt:  effRel = Relation::Geq; break;
                case Relation::Leq: effRel = Relation::Gt; break;
                case Relation::Gt:  effRel = Relation::Leq; break;
                case Relation::Geq: effRel = Relation::Lt; break;
            }
        }

        // Register variables
        for (const auto& [name, coeff] : p.lhs.terms) {
            (void)coeff;
            if (nameToIdx.count(name)) continue;
            auto kind = isIntegerVar(name)
                ? InternalMilpEngine::VarKind::Int
                : InternalMilpEngine::VarKind::Real;
            int idx = milpEngine_.addVar(name, kind);
            nameToIdx[name] = idx;
        }

        if (effRel == Relation::Neq) {
            disequalities_.push_back({p.lhs, p.rhs, a.lit});
        } else {
            InternalMilpEngine::LinearConstraint c;
            for (const auto& [name, coeff] : p.lhs.terms) {
                c.terms.push_back({nameToIdx[name], coeff});
            }
            c.rhs = p.rhs;
            c.rel = effRel;
            c.reason = a.lit;
            milpEngine_.addConstraint(c);
        }
    }

    auto r = milpEngine_.solve(InternalMilpEngine::MilpMode::Budgeted);

    switch (r.kind) {
        case InternalMilpEngine::MilpResult::Kind::Unsat: {
            auto tc = TheoryConflict{};
            auto precise = milpEngine_.getConflictReasons();
            if (!precise.empty()) {
                tc.clause = precise;
            } else {
                tc.clause = allActiveReasons();
            }
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
        case InternalMilpEngine::MilpResult::Kind::Unknown:
            return TheoryCheckResult::unknown();

        case InternalMilpEngine::MilpResult::Kind::Sat: {
            // Validate disequalities using full DeltaRational values
            for (const auto& d : disequalities_) {
                DeltaRational val;
                for (const auto& [name, coeff] : d.lhs.terms) {
                    auto it = nameToIdx.find(name);
                    if (it != nameToIdx.end()) {
                        auto dv = milpEngine_.deltaValue(it->second);
                        val.a += dv.a * coeff;
                        val.b += dv.b * coeff;
                    }
                }
                val.a -= d.rhs;
                if (val.isZero()) {
                    auto litLt = registry_->getOrCreateLinearBoundAtom(
                        d.lhs, Relation::Lt, d.rhs, TheoryId::LIRA);
                    auto litGt = registry_->getOrCreateLinearBoundAtom(
                        d.lhs, Relation::Gt, d.rhs, TheoryId::LIRA);
                    return TheoryCheckResult::mkLemma(TheoryLemma{{litLt, litGt}});
                }
            }
            return TheoryCheckResult::consistent();
        }

        case InternalMilpEngine::MilpResult::Kind::NeedBranch: {
            if (!registry_) return TheoryCheckResult::unknown();
            std::string name = std::string(milpEngine_.varName(r.branchVar));
            if (name.empty()) return TheoryCheckResult::unknown();
            LinearFormKey form;
            form.terms.push_back({name, mpq_class(1)});
            auto litLo = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Leq, r.floorVal, TheoryId::LIRA);
            auto litHi = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Geq, r.ceilVal, TheoryId::LIRA);
            return TheoryCheckResult::mkLemma(TheoryLemma{{litLo, litHi}});
        }
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult LiraSolver::checkFullEffort(TheoryLemmaStorage& /*lemmaDb*/) {
    milpEngine_.clear();
    disequalities_.clear();
    std::unordered_map<std::string, int> nameToIdx;

    for (const auto& a : trail()) {
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);

        Relation effRel = p.rel;
        if (!a.value) {
            switch (p.rel) {
                case Relation::Eq:  effRel = Relation::Neq; break;
                case Relation::Neq: effRel = Relation::Eq; break;
                case Relation::Lt:  effRel = Relation::Geq; break;
                case Relation::Leq: effRel = Relation::Gt; break;
                case Relation::Gt:  effRel = Relation::Leq; break;
                case Relation::Geq: effRel = Relation::Lt; break;
            }
        }

        for (const auto& [name, coeff] : p.lhs.terms) {
            (void)coeff;
            if (nameToIdx.count(name)) continue;
            auto kind = isIntegerVar(name)
                ? InternalMilpEngine::VarKind::Int
                : InternalMilpEngine::VarKind::Real;
            int idx = milpEngine_.addVar(name, kind);
            nameToIdx[name] = idx;
        }

        if (effRel == Relation::Neq) {
            disequalities_.push_back({p.lhs, p.rhs, a.lit});
        } else {
            InternalMilpEngine::LinearConstraint c;
            for (const auto& [name, coeff] : p.lhs.terms) {
                c.terms.push_back({nameToIdx[name], coeff});
            }
            c.rhs = p.rhs;
            c.rel = effRel;
            c.reason = a.lit;
            milpEngine_.addConstraint(c);
        }
    }

    auto r = milpEngine_.solve(InternalMilpEngine::MilpMode::Complete);

    switch (r.kind) {
        case InternalMilpEngine::MilpResult::Kind::Sat: {
            // Validate disequalities using full DeltaRational values
            for (const auto& d : disequalities_) {
                DeltaRational val;
                for (const auto& [name, coeff] : d.lhs.terms) {
                    auto it = nameToIdx.find(name);
                    if (it != nameToIdx.end()) {
                        auto dv = milpEngine_.deltaValue(it->second);
                        val.a += dv.a * coeff;
                        val.b += dv.b * coeff;
                    }
                }
                val.a -= d.rhs;
                if (val.isZero()) {
                    auto litLt = registry_->getOrCreateLinearBoundAtom(
                        d.lhs, Relation::Lt, d.rhs, TheoryId::LIRA);
                    auto litGt = registry_->getOrCreateLinearBoundAtom(
                        d.lhs, Relation::Gt, d.rhs, TheoryId::LIRA);
                    return TheoryCheckResult::mkLemma(TheoryLemma{{litLt, litGt}});
                }
            }
            return TheoryCheckResult::consistent();
        }
        case InternalMilpEngine::MilpResult::Kind::Unsat: {
            auto tc = TheoryConflict{};
            auto precise = milpEngine_.getConflictReasons();
            if (!precise.empty()) {
                tc.clause = precise;
            } else {
                tc.clause = allActiveReasons();
            }
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
        default:
            return TheoryCheckResult::unknown();
    }
}

void LiraSolver::onReset() {
    // Base clears the trail; clear LIRA-specific state here.
    disequalities_.clear();
    milpEngine_.clear();
}

void LiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

void LiraSolver::setCoreIr(const CoreIr* ir) {
    coreIr_ = ir;
}

std::optional<TheorySolver::TheoryModel> LiraSolver::getModel() const {
    TheoryModel model;
    int n = milpEngine_.numVars();
    for (int i = 0; i < n; ++i) {
        std::string name = std::string(milpEngine_.varName(i));
        if (name.empty()) continue;
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;
        mpq_class val = milpEngine_.value(i);
        if (val.get_den() == 1) {
            model.assignments[name] = val.get_num().get_str();
        } else {
            model.assignments[name] = val.get_str();
        }
        model.numericAssignments.insert({name, RealValue::fromMpq(val)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

std::vector<SatLit> LiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : trail()) {
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



} // namespace nlcolver
