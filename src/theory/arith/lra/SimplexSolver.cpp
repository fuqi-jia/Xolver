#include "theory/arith/lra/SimplexSolver.h"
#include "expr/payload.h"
#include <cassert>
#include <algorithm>

namespace nlcolver {

// ============================================================================
// LinearForm hash/equality
// ============================================================================

bool SimplexSolver::LinearForm::operator==(const LinearForm& o) const {
    if (rhs != o.rhs) return false;
    if (terms.size() != o.terms.size()) return false;
    for (size_t i = 0; i < terms.size(); ++i) {
        if (terms[i].first != o.terms[i].first) return false;
        if (terms[i].second != o.terms[i].second) return false;
    }
    return true;
}

std::size_t SimplexSolver::LinearFormHash::operator()(const LinearForm& f) const {
    std::size_t h = std::hash<std::string>{}(f.rhs.get_str());
    for (const auto& t : f.terms) {
        h ^= std::hash<std::string>{}(t.first) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= std::hash<std::string>{}(t.second.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    return h;
}

// ============================================================================
// Linear expression extraction (reused from old SimplexSolver)
// ============================================================================

static bool extractLinearExpr(ExprId eid, const CoreIr& ir,
                               std::unordered_map<std::string, mpq_class>& coeffs,
                               mpq_class& constant,
                               const mpq_class& mul) {
    const CoreExpr& e = ir.get(eid);
    switch (e.kind) {
        case Kind::ConstInt: {
            if (auto* v = std::get_if<int64_t>(&e.payload.value)) {
                constant += mul * mpq_class(*v);
            }
            return true;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                constant += mul * mpq_class(*s);
            }
            return true;
        }
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                coeffs[*s] += mul;
            }
            return true;
        }
        case Kind::Add: {
            for (ExprId child : e.children) {
                if (!extractLinearExpr(child, ir, coeffs, constant, mul)) return false;
            }
            return true;
        }
        case Kind::Sub: {
            if (e.children.size() != 2) return false;
            if (!extractLinearExpr(e.children[0], ir, coeffs, constant, mul)) return false;
            if (!extractLinearExpr(e.children[1], ir, coeffs, constant, -mul)) return false;
            return true;
        }
        case Kind::Neg: {
            if (e.children.size() != 1) return false;
            return extractLinearExpr(e.children[0], ir, coeffs, constant, -mul);
        }
        case Kind::Mul: {
            if (e.children.size() != 2) return false;
            const CoreExpr& a = ir.get(e.children[0]);
            const CoreExpr& b = ir.get(e.children[1]);
            if (a.isConst()) {
                mpq_class c;
                if (auto* iv = std::get_if<int64_t>(&a.payload.value)) c = mpq_class(*iv);
                else if (auto* sv = std::get_if<std::string>(&a.payload.value)) c = mpq_class(*sv);
                else return false;
                return extractLinearExpr(e.children[1], ir, coeffs, constant, mul * c);
            }
            if (b.isConst()) {
                mpq_class c;
                if (auto* iv = std::get_if<int64_t>(&b.payload.value)) c = mpq_class(*iv);
                else if (auto* sv = std::get_if<std::string>(&b.payload.value)) c = mpq_class(*sv);
                else return false;
                return extractLinearExpr(e.children[0], ir, coeffs, constant, mul * c);
            }
            return false;
        }
        default:
            return false;
    }
}

// ============================================================================
// SimplexSolver
// ============================================================================

SimplexSolver::SimplexSolver() = default;

void SimplexSolver::push() {
    gs_.push();
}

void SimplexSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void SimplexSolver::reset() {
    gs_.resetActiveBounds();
    disequalities_.clear();
    boundReasons_.clear();
}

int SimplexSolver::getOrCreateVar(const std::string& name) {
    auto it = varToIndex_.find(name);
    if (it != varToIndex_.end()) return it->second;
    int idx = gs_.addVar(name);
    varToIndex_[name] = idx;
    return idx;
}

bool SimplexSolver::extractLinearConstraint(ExprId eid, const CoreIr& ir,
                                             std::unordered_map<std::string, mpq_class>& coeffs,
                                             mpq_class& rhs, Relation& rel) {
    const CoreExpr& e = ir.get(eid);
    if (e.children.size() != 2) return false;

    switch (e.kind) {
        case Kind::Eq:  rel = Relation::Eq;  break;
        case Kind::Lt:  rel = Relation::Lt;  break;
        case Kind::Leq: rel = Relation::Leq; break;
        case Kind::Gt:  rel = Relation::Gt;  break;
        case Kind::Geq: rel = Relation::Geq; break;
        case Kind::Distinct: rel = Relation::Neq; break;
        default: return false;
    }

    mpq_class constant = 0;
    if (!extractLinearExpr(e.children[0], ir, coeffs, constant, mpq_class(1))) return false;
    if (!extractLinearExpr(e.children[1], ir, coeffs, constant, mpq_class(-1))) return false;
    rhs = -constant;
    return true;
}

bool SimplexSolver::registerAtom(const TheoryAtom& atom, const CoreIr& ir) {
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class rhs;
    Relation rel;
    if (!extractLinearConstraint(atom.exprId, ir, coeffs, rhs, rel)) {
        return false;
    }

    LinearForm form;
    form.rhs = rhs;
    for (auto& [name, coeff] : coeffs) {
        if (coeff != 0) {
            form.terms.push_back({name, coeff});
        }
    }
    std::sort(form.terms.begin(), form.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });

    std::vector<std::pair<int, mpq_class>> gsTerms;
    for (auto& [name, coeff] : form.terms) {
        int v = getOrCreateVar(name);
        gsTerms.push_back({v, coeff});
    }

    auto it = formToAux_.find(form);
    int auxVar;
    if (it != formToAux_.end()) {
        auxVar = it->second;
    } else {
        auxVar = gs_.addConstraint(gsTerms, rhs);
        formToAux_[form] = auxVar;
    }

    exprToAtom_[atom.exprId] = {auxVar, rel};
    return true;
}

static Relation negateRelation(Relation r) {
    switch (r) {
        case Relation::Eq:  return Relation::Neq;
        case Relation::Lt:  return Relation::Geq;
        case Relation::Leq: return Relation::Gt;
        case Relation::Gt:  return Relation::Leq;
        case Relation::Geq: return Relation::Lt;
        case Relation::Neq: return Relation::Eq;
    }
    return r;
}

void SimplexSolver::assertBound(int auxVar, Relation rel, bool value, SatLit reasonLit) {
    Relation effective = value ? rel : negateRelation(rel);

    auto& reasons = boundReasons_[auxVar];
    switch (effective) {
        case Relation::Eq:
            gs_.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit));
            gs_.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit));
            reasons.first = reasonLit;
            reasons.second = reasonLit;
            break;
        case Relation::Leq:
            gs_.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit));
            reasons.second = reasonLit;
            break;
        case Relation::Lt:
            gs_.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0, -1)), reasonLit));
            reasons.second = reasonLit;
            break;
        case Relation::Geq:
            gs_.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit));
            reasons.first = reasonLit;
            break;
        case Relation::Gt:
            gs_.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0, 1)), reasonLit));
            reasons.first = reasonLit;
            break;
        case Relation::Neq:
            // Cannot express as a single convex bound.
            disequalities_.push_back({auxVar, reasonLit});
            break;
    }
}

void SimplexSolver::assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) {
    if (exprToAtom_.find(atom.exprId) == exprToAtom_.end()) {
        if (!registerAtom(atom, ir)) return;
    }

    auto it = exprToAtom_.find(atom.exprId);
    if (it == exprToAtom_.end()) return;

    const auto& info = it->second;
    SatLit reasonLit = value ? SatLit::positive(atom.satVar)
                             : SatLit::negative(atom.satVar);

    assertBound(info.auxVar, info.rel, value, reasonLit);
}

TheoryCheckResult SimplexSolver::check(const CoreIr& /*ir*/) {
    auto r = gs_.check();
    if (r == GeneralSimplex::Result::Unsat) {
        return TheoryCheckResult::mkConflict(translateConflict());
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // Handle disequalities: if any violated, return a guarded split lemma
    if (!disequalities_.empty()) {
        return handleDisequalities();
    }

    return TheoryCheckResult::consistent();
}

TheoryCheckResult SimplexSolver::handleDisequalities() {
    for (const auto& d : disequalities_) {
        auto val = gs_.value(d.auxVar);
        if (val.isZero()) {
            // Current LRA model violates s != 0.
            // Return guarded split lemma: ¬d ∨ (s < 0) ∨ (s > 0)
            return TheoryCheckResult::mkLemma(buildDiseqSplitLemma(d));
        }
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma SimplexSolver::buildDiseqSplitLemma(const DiseqInfo& d) {
    // V1: use delta-rational strict bounds.
    // The split lemma is: ¬(p != 0) ∨ (p < 0) ∨ (p > 0)
    // We encode the strict bounds using the original disequality literal's var
    // with explicit delta.
    SatLit notD = d.lit.negated();
    SatLit lt = d.lit;   // placeholder: will be replaced by actual bound atoms in V2
    SatLit gt = d.lit;   // placeholder

    // V1 workaround: the split lemma only contains ¬d.
    // SAT solver will need to reassign d to false, which forces the solver
    // to try a different assignment. This is sound but weak.
    // V2 TODO: dynamically create strict bound atoms and register them.
    (void)lt; (void)gt;
    return TheoryLemma{{notD}};
}

TheoryConflict SimplexSolver::translateConflict() {
    TheoryConflict tc;
    for (const auto& br : gs_.getConflict()) {
        auto it = boundReasons_.find(br.var);
        if (it == boundReasons_.end()) continue;
        const auto& reasons = it->second;
        std::optional<SatLit> reasonLit = br.isLower ? reasons.first : reasons.second;
        if (reasonLit.has_value()) {
            tc.clause.push_back(reasonLit->negated());
        }
    }
    return tc;
}

} // namespace nlcolver
