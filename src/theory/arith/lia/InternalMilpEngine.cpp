#include "theory/arith/lia/InternalMilpEngine.h"
#include <algorithm>

namespace nlcolver {

void InternalMilpEngine::clear() {
    simplex_.reset();
    varNames_.clear();
    varKinds_.clear();
    constraints_.clear();
    integerVars_.clear();
}

void InternalMilpEngine::push() {
    simplex_.push();
}

void InternalMilpEngine::pop() {
    simplex_.pop();
}

int InternalMilpEngine::addVar(std::string_view name, VarKind kind) {
    int idx = static_cast<int>(varNames_.size());
    varNames_.push_back(std::string(name));
    varKinds_.push_back(kind);
    simplex_.addVar(std::string(name));
    if (kind == VarKind::Int) {
        integerVars_.insert(idx);
    }
    return idx;
}

std::string_view InternalMilpEngine::varName(int var) const {
    if (var < 0 || var >= (int)varNames_.size()) return "";
    return varNames_[var];
}

void InternalMilpEngine::addConstraint(const LinearConstraint& c) {
    constraints_.push_back(c);
}

InternalMilpEngine::MilpResult InternalMilpEngine::solve(MilpMode mode) {
    auto r = solveLpRelaxation();
    if (r.kind != MilpResult::Kind::Sat) return r;

    switch (mode) {
        case MilpMode::RelaxationOnly:
            return r;
        case MilpMode::Budgeted: {
            int budget = FAST_BRANCH_BUDGET;
            auto ir = checkIntegrality(/*useBudget=*/true, budget);
            return ir;
        }
        case MilpMode::Complete: {
            int budget = -1;
            auto ir = checkIntegrality(/*useBudget=*/false, budget);
            return ir;
        }
    }
    return r; // unreachable
}

InternalMilpEngine::MilpResult InternalMilpEngine::solveLpRelaxation() {
    simplex_.resetActiveBounds();
    SatLit dummyReason{0, true};

    for (const auto& c : constraints_) {
        int aux = simplex_.addConstraint(c.terms, c.rhs);
        if (aux < 0) continue;

        switch (c.rel) {
            case Relation::Eq:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), dummyReason));
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), dummyReason));
                break;
            case Relation::Leq:
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), dummyReason));
                break;
            case Relation::Lt:
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0, -1)), dummyReason));
                break;
            case Relation::Geq:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), dummyReason));
                break;
            case Relation::Gt:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0, 1)), dummyReason));
                break;
            case Relation::Neq:
                // Neq is not supported at engine level; caller must split
                break;
        }
    }

    auto r = simplex_.check();
    if (r == GeneralSimplex::Result::Unsat) return {MilpResult::Kind::Unsat, -1, {}, {}};
    if (r == GeneralSimplex::Result::Unknown) return {MilpResult::Kind::Unknown, -1, {}, {}};
    return {MilpResult::Kind::Sat, -1, {}, {}};
}

int InternalMilpEngine::findBestFractionalVar(mpq_class& outFrac) const {
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int v : integerVars_) {
        auto val = simplex_.value(v);
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
                bestVar = v;
            }
        }
    }

    outFrac = bestFrac;
    return bestVar;
}

void InternalMilpEngine::computeFloorCeil(const DeltaRational& val,
                                          mpq_class& floorVal,
                                          mpq_class& ceilVal) const {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

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
}

InternalMilpEngine::MilpResult InternalMilpEngine::checkIntegrality(bool useBudget, int& budget) {
    mpq_class frac;
    int bestVar = findBestFractionalVar(frac);

    if (bestVar == -1) {
        return {MilpResult::Kind::Sat, -1, {}, {}};
    }

    if (useBudget && budget <= 0) {
        auto val = simplex_.value(bestVar);
        mpq_class floorVal, ceilVal;
        computeFloorCeil(val, floorVal, ceilVal);
        return {MilpResult::Kind::NeedBranch, bestVar, floorVal, ceilVal};
    }
    if (useBudget) --budget;

    return dfsCheckIntegrality(useBudget, budget);
}

InternalMilpEngine::MilpResult InternalMilpEngine::dfsCheckIntegrality(bool useBudget, int& budget) {
    mpq_class frac;
    int bestVar = findBestFractionalVar(frac);

    if (bestVar == -1) {
        return {MilpResult::Kind::Sat, -1, {}, {}};
    }

    if (useBudget && budget <= 0) {
        auto val = simplex_.value(bestVar);
        mpq_class floorVal, ceilVal;
        computeFloorCeil(val, floorVal, ceilVal);
        return {MilpResult::Kind::NeedBranch, bestVar, floorVal, ceilVal};
    }
    if (useBudget) --budget;

    auto val = simplex_.value(bestVar);
    mpq_class floorVal, ceilVal;
    computeFloorCeil(val, floorVal, ceilVal);

    SatLit dummyReason{0, true};

    // Branch 1: x <= floor
    simplex_.push();
    bool ok1 = simplex_.assertUpper(bestVar, BoundInfo(BoundValue(DeltaRational(floorVal)), dummyReason));
    if (ok1) {
        auto r1 = simplex_.check();
        if (r1 == GeneralSimplex::Result::Sat) {
            auto sub = dfsCheckIntegrality(useBudget, budget);
            if (sub.kind == MilpResult::Kind::Sat || sub.kind == MilpResult::Kind::Unknown) {
                return sub;
            }
        } else if (r1 == GeneralSimplex::Result::Unknown) {
            simplex_.pop();
            return {MilpResult::Kind::Unknown, -1, {}, {}};
        }
    }
    simplex_.pop();

    // Branch 2: x >= ceil
    simplex_.push();
    bool ok2 = simplex_.assertLower(bestVar, BoundInfo(BoundValue(DeltaRational(ceilVal)), dummyReason));
    if (ok2) {
        auto r2 = simplex_.check();
        if (r2 == GeneralSimplex::Result::Sat) {
            auto sub = dfsCheckIntegrality(useBudget, budget);
            if (sub.kind == MilpResult::Kind::Sat || sub.kind == MilpResult::Kind::Unknown) {
                return sub;
            }
        } else if (r2 == GeneralSimplex::Result::Unknown) {
            simplex_.pop();
            return {MilpResult::Kind::Unknown, -1, {}, {}};
        }
    }
    simplex_.pop();

    return {MilpResult::Kind::Unsat, -1, {}, {}};
}

mpq_class InternalMilpEngine::value(int var) const {
    auto dr = simplex_.value(var);
    return dr.a;
}

DeltaRational InternalMilpEngine::deltaValue(int var) const {
    return simplex_.value(var);
}

} // namespace nlcolver
