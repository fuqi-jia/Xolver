#include "theory/arith/lia/LiaSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include <cassert>
#include <algorithm>
#include <iostream>

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
}

void LiaSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void LiaSolver::backtrackToLevel(int level) {
    currentLevel_ = level;
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());

    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}

TheoryCheckResult LiaSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    // Rebuild all state from current active assignments.
    gs_.resetActiveBounds();
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

        Relation effectiveRel = a.value ? payload.rel : negateRelation(payload.rel);
        if (effectiveRel == Relation::Neq) {
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

    // Apply interface equalities from Nelson-Oppen combination
    for (const auto& ieq : interfaceEqualities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            bool ok = true;
            ok = gs_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            ok = gs_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                tc.clause.push_back(ieq.reason);
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    auto r = gs_.check();
    if (r == GeneralSimplex::Result::Unsat) {
        auto tc = TheoryConflict{};
        const auto& conflict = gs_.getConflict();
        if (!conflict.empty()) {
            for (const auto& cr : conflict) {
                tc.clause.push_back(cr.reason);
            }
        } else {
            tc.clause = allActiveReasons();
        }
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // P3: Check interface disequalities. LIA is non-convex; if any
    // interface disequality is violated by the simplex model, we cannot
    // emit a split lemma without arrangement. Return Unknown conservatively.
    for (const auto& ieq : interfaceDisequalities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            auto val = gs_.value(aux);
            if (val.isZero()) {
                return TheoryCheckResult::unknown();
            }
        }
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

TheoryCheckResult LiaSolver::handleDisequalities(TheoryLemmaStorage& lemmaDb) {
    return handleSimplexDisequalities(
        disequalities_, gs_, lemmaDb,
        [this](const DiseqInfo& d) -> TheoryCheckResult {
            // If the disequality is forced to be false by current bounds
            // (auxVar is fixed to 0), return a precise conflict.
            auto fixed = gs_.fixedValue(d.auxVar);
            if (fixed && fixed->isZero()) {
                auto reasons = gs_.explainFixedValue(d.auxVar);
                TheoryConflict tc;
                for (const auto& br : reasons) {
                    tc.clause.push_back(br.reason);
                }
                tc.clause.push_back(d.lit);
                return TheoryCheckResult::mkConflict(std::move(tc));
            }

            if (d.rhs.get_den() != 1) {
                return TheoryCheckResult::consistent();
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
                        TheoryConflict{{d.lit}});
                }
                return TheoryCheckResult::consistent();
            }

            if (c % g != 0) {
                return TheoryCheckResult::consistent();
            }

            assert(registry_ != nullptr);
            mpq_class leRhs = mpq_class(c - g, 1);
            mpq_class geRhs = mpq_class(c + g, 1);

            auto lit1 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Leq, leRhs, TheoryId::LIA);
            auto lit2 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Geq, geRhs, TheoryId::LIA);

            return TheoryCheckResult::mkLemma(
                TheoryLemma{{d.lit.negated(), lit1, lit2}});
        });
}

TheoryCheckResult LiaSolver::checkIntegrality(TheoryLemmaStorage& /*lemmaDb*/) {
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int v : integerVars_) {
        auto val = gs_.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            mpq_class frac;
            if (val.b != 0) {
                // Delta-rational: value is a + b·δ where δ is infinitesimal.
                // If b > 0, value is just above a (frac ≈ 1).
                // If b < 0, value is just below a (frac ≈ 0).
                // Use 1/2 as a representative fractional distance.
                frac = mpq_class(1, 2);
            } else {
                // Compute fractional part = |val.a - floor(val.a)|
                mpz_class num = val.a.get_num();
                mpz_class den = val.a.get_den();
                mpz_class f = num / den;  // truncates toward zero
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
                bestVar = v;
            }
        }
    }

    if (bestVar != -1) {
        assert(registry_ != nullptr);
        return TheoryCheckResult::mkLemma(buildBranchSplitLemma(bestVar, gs_.value(bestVar)));
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma LiaSolver::buildBranchSplitLemma(int var, const DeltaRational& val) {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        if (val.b > 0) {
            // value = a + epsilon, strictly greater than a
            floorVal = q;
            ceilVal = mpq_class(num + 1, 1);
        } else if (val.b < 0) {
            // value = a - epsilon, strictly less than a
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

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (experimental skeleton for non-convex LIA)
// ---------------------------------------------------------------------------

std::string LiaSolver::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = coreIr_->get(st->coreExpr);
    std::string name;
    if (expr.kind == Kind::Variable) {
        if (std::holds_alternative<std::string>(expr.payload.value)) {
            name = std::get<std::string>(expr.payload.value);
        }
    } else if (expr.isConst()) {
        // Constants participate in interface equalities via a synthetic variable.
        // The actual constant value is enforced via bound assertion in check().
        name = "__const_" + st->name;
    }
    if (!name.empty()) {
        sharedTermToVarName_[s] = name;
    }
    return name;
}

int LiaSolver::getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = interfaceEqAuxVars_.find(key);
    if (it != interfaceEqAuxVars_.end()) return it->second;

    std::string va = getVarNameForSharedTerm(a);
    std::string vb = getVarNameForSharedTerm(b);

    bool aIsConst = false, bIsConst = false;
    mpq_class aVal, bVal;
    if (sharedTermRegistry_ && coreIr_) {
        if (const auto* stA = sharedTermRegistry_->get(a)) {
            const auto& exprA = coreIr_->get(stA->coreExpr);
            std::cerr << "[LIA-AUX] a=" << a << " expr=" << stA->coreExpr << " kind=" << (int)exprA.kind << " name=" << stA->name << "\n";
            if (exprA.isConst()) {
                aIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprA.payload.value)) aVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprA.payload.value)) aVal = mpq_class(*s);
            }
        }
        if (const auto* stB = sharedTermRegistry_->get(b)) {
            const auto& exprB = coreIr_->get(stB->coreExpr);
            std::cerr << "[LIA-AUX] b=" << b << " expr=" << stB->coreExpr << " kind=" << (int)exprB.kind << " name=" << stB->name << "\n";
            if (exprB.isConst()) {
                bIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprB.payload.value)) bVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprB.payload.value)) bVal = mpq_class(*s);
            }
        }
    }

    int aux = -1;
    if (aIsConst && bIsConst) {
        if (aVal == bVal) return -1;
        return -1;
    } else if (aIsConst) {
        if (vb.empty()) return -1;
        int vB = manager_.getOrCreateVar(gs_, vb);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vB, mpq_class(1)});
        aux = gs_.addConstraint(terms, aVal);
    } else if (bIsConst) {
        if (va.empty()) return -1;
        int vA = manager_.getOrCreateVar(gs_, va);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vA, mpq_class(1)});
        aux = gs_.addConstraint(terms, bVal);
    } else {
        if (va.empty() || vb.empty()) return -1;
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
        aux = gs_.addConstraint(terms, mpq_class(0));
    }

    interfaceEqAuxVars_[key] = aux;
    return aux;
}

TheoryCheckResult LiaSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    std::cerr << "[LIA-IEQ] EQ a=" << a << " b=" << b << " aux=" << aux << " reason=" << (reason.sign?"+":"") << reason.var << "\n";
    if (aux < 0) return TheoryCheckResult::consistent();

    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
LiaSolver::getDeducedSharedEqualities() {
    // P3: LIA is non-convex; deducing single equalities from a convex
    // simplex model is unsound without arrangement. Return empty.
    return {};
}

std::vector<SatLit> LiaSolver::allActiveReasons() const {
    std::vector<SatLit> rs;
    rs.reserve(activeAssignments_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    for (const auto& a : activeAssignments_) {
        rs.push_back(a.lit);
    }
    for (const auto& ieq : interfaceEqualities_) {
        rs.push_back(ieq.reason);
    }
    for (const auto& idiseq : interfaceDisequalities_) {
        rs.push_back(idiseq.reason);
    }
    std::sort(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    rs.erase(std::unique(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), rs.end());
    return rs;
}

std::optional<TheorySolver::TheoryModel> LiaSolver::getModel() const {
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;           // skip auxiliary vars
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue; // internal
        DeltaRational val = gs_.value(i);
        // For integer variables, value should be integral after check().
        // If delta component is non-zero, take the rational part (delta is infinitesimal).
        if (val.b == 0 && val.a.get_den() == 1) {
            model.assignments[name] = val.a.get_num().get_str();
        } else {
            model.assignments[name] = val.a.get_str();
        }
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

} // namespace nlcolver
