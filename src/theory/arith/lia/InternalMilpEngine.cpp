#include "theory/arith/lia/InternalMilpEngine.h"
#include <algorithm>
#include <iostream>

namespace nlcolver {

void InternalMilpEngine::clear() {
    simplex_.reset();
    varNames_.clear();
    varKinds_.clear();
    constraints_.clear();
    integerVars_.clear();
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

void InternalMilpEngine::addConstraint(const LinearConstraint& c) {
    constraints_.push_back(c);
}

InternalMilpEngine::Result InternalMilpEngine::checkRelaxation() {
    return solveLpRelaxation();
}

InternalMilpEngine::Result InternalMilpEngine::checkFast() {
    auto r = solveLpRelaxation();
    if (r != Result::Sat) return r;
    return checkIntegrality(/*useBudget=*/true);
}

InternalMilpEngine::Result InternalMilpEngine::checkComplete() {
    auto r = solveLpRelaxation();
    if (r != Result::Sat) return r;
    return checkIntegrality(/*useBudget=*/false);
}

InternalMilpEngine::Result InternalMilpEngine::solveLpRelaxation() {
    simplex_.resetActiveBounds();

    for (const auto& c : constraints_) {
        int aux = simplex_.addConstraint(c.terms, c.rhs);
        if (aux < 0) continue;

        switch (c.rel) {
            case Relation::Eq:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
                break;
            case Relation::Leq:
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
                break;
            case Relation::Lt:
                simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0, -1))));
                break;
            case Relation::Geq:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
                break;
            case Relation::Gt:
                simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0, 1))));
                break;
            case Relation::Neq:
                // Neq is not supported at engine level; caller must split
                break;
        }
    }

    auto r = simplex_.check();
    if (r == GeneralSimplex::Result::Unsat) return Result::Unsat;
    if (r == GeneralSimplex::Result::Unknown) return Result::Unknown;
    return Result::Sat;
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

InternalMilpEngine::Result InternalMilpEngine::checkIntegrality(bool useBudget) {
    int budget = useBudget ? FAST_BRANCH_BUDGET : -1;

    struct BranchState {
        std::vector<std::pair<int, BoundInfo>> addedBounds;
    };
    std::vector<BranchState> stack;

    while (true) {
        mpq_class frac;
        int bestVar = findBestFractionalVar(frac);

        if (bestVar == -1) {
            // All integer variables are integral
            return Result::Sat;
        }

        if (useBudget && budget <= 0) {
            return Result::Unknown;
        }
        if (useBudget) --budget;

        auto val = simplex_.value(bestVar);
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

        // Branch 1: x <= floor
        bool ok1 = simplex_.assertUpper(bestVar, BoundInfo(BoundValue(DeltaRational(floorVal))));
        if (ok1) {
            auto r1 = simplex_.check();
            if (r1 == GeneralSimplex::Result::Sat) {
                continue; // check again for more fractional vars
            }
            if (r1 == GeneralSimplex::Result::Unknown) {
                return Result::Unknown;
            }
        }

        // Branch 1 failed, try Branch 2: x >= ceil
        simplex_.backtrackToLevel(0); // reset bounds added in this branch
        simplex_.resetActiveBounds();
        // Re-apply all original constraints
        for (const auto& c : constraints_) {
            int aux = simplex_.addConstraint(c.terms, c.rhs);
            if (aux < 0) continue;
            switch (c.rel) {
                case Relation::Eq:
                    simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
                    simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
                    break;
                case Relation::Leq:
                    simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
                    break;
                case Relation::Lt:
                    simplex_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0, -1))));
                    break;
                case Relation::Geq:
                    simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
                    break;
                case Relation::Gt:
                    simplex_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0, 1))));
                    break;
                default: break;
            }
        }

        bool ok2 = simplex_.assertLower(bestVar, BoundInfo(BoundValue(DeltaRational(ceilVal))));
        if (ok2) {
            auto r2 = simplex_.check();
            if (r2 == GeneralSimplex::Result::Sat) {
                continue;
            }
            if (r2 == GeneralSimplex::Result::Unknown) {
                return Result::Unknown;
            }
        }

        // Both branches failed
        return Result::Unsat;
    }
}

mpq_class InternalMilpEngine::value(int var) const {
    auto dr = simplex_.value(var);
    return dr.a;
}

} // namespace nlcolver
