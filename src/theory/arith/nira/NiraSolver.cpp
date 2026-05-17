#include "theory/arith/nira/NiraSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "expr/ir.h"
#include <algorithm>
#include <functional>
#include <iostream>

namespace nlcolver {

NiraSolver::NiraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)) {
    if (kernel_) {
        converter_ = std::make_unique<PolynomialConverter>(*kernel_);
    }
}

NiraSolver::~NiraSolver() = default;

void NiraSolver::push() {
    gsRelax_.push();
}

void NiraSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gsRelax_.pop();
    }
}

void NiraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void NiraSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
    gsRelax_.backtrackToLevel(level);
}

TheoryCheckResult NiraSolver::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort) {
    if (activeAssignments_.empty()) {
        return TheoryCheckResult::consistent();
    }

    // --- Presolve: fixed-value substitution ---
    if (kernel_) {
        std::unordered_map<std::string, mpq_class> fixedValues;

        // Step 1: collect fixed values from linear equalities
        for (const auto& a : activeAssignments_) {
            if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
            if (payload.rel != Relation::Eq) continue;
            if (payload.lhs.terms.size() != 1) continue;

            const auto& term = payload.lhs.terms[0];
            if (term.second == 0) continue;
            fixedValues[term.first] = payload.rhs / term.second;
        }

        // Step 2: substitute into polynomial constraints
        for (const auto& a : activeAssignments_) {
            if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<PolynomialAtomPayload>(a.atom.payload);
            PolyId current = payload.poly;

            for (const auto& [name, value] : fixedValues) {
                auto varIdOpt = kernel_->findVar(name);
                if (!varIdOpt) continue;
                auto substituted = kernel_->substituteRational(current, *varIdOpt, value);
                if (substituted) current = *substituted;
            }

            if (kernel_->isConstant(current)) {
                mpq_class val = kernel_->toConstant(current);
                bool satisfied = false;
                switch (payload.rel) {
                    case Relation::Eq:  satisfied = (val == 0); break;
                    case Relation::Neq: satisfied = (val != 0); break;
                    case Relation::Lt:  satisfied = (val < 0); break;
                    case Relation::Leq: satisfied = (val <= 0); break;
                    case Relation::Gt:  satisfied = (val > 0); break;
                    case Relation::Geq: satisfied = (val >= 0); break;
                }
                if (!satisfied) {
                    return TheoryCheckResult::mkConflict(TheoryConflict{{a.lit}});
                }
            }
        }
    }

    // --- Full effort: bounded-complete enumeration ---
    if (effort == TheoryEffort::Full) {
        auto r = checkBoundedComplete(lemmaDb);
        if (r.kind == TheoryCheckResult::Kind::Consistent) return r;
    }

    // TODO: classify, pure subproblem delegation, relaxation
    return TheoryCheckResult::unknown();
}

TheoryCheckResult NiraSolver::checkPureSubproblems(TheoryLemmaDatabase& /*lemmaDb*/) {
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NiraSolver::checkRelaxationAndValidate(TheoryLemmaDatabase& /*lemmaDb*/) {
    return TheoryCheckResult::unknown();
}

namespace {

bool isIntegerVar(const CoreIr* coreIr, const std::string& name) {
    if (!coreIr) return false;
    for (size_t i = 0; i < coreIr->size(); ++i) {
        ExprId eid = static_cast<ExprId>(i);
        const auto& expr = coreIr->get(eid);
        if (expr.kind == Kind::Variable) {
            if (std::holds_alternative<std::string>(expr.payload.value)) {
                if (std::get<std::string>(expr.payload.value) == name) {
                    return expr.sort == coreIr->intSortId();
                }
            }
        }
    }
    return false;
}

// Try to convert a substituted polynomial to a linear form.
// Returns nullopt if the polynomial is not linear.
std::optional<std::pair<LinearFormKey, mpq_class>> polyToLinearForm(
    const PolynomialKernel* kernel, PolyId poly) {
    auto termsOpt = kernel->terms(poly);
    if (!termsOpt) return std::nullopt;

    LinearFormKey lhs;
    mpq_class rhs = 0;

    for (const auto& term : *termsOpt) {
        if (term.powers.empty()) {
            rhs -= mpq_class(term.coefficient);
        } else if (term.powers.size() == 1 && term.powers[0].second == 1) {
            auto varName = kernel->varName(term.powers[0].first);
            lhs.terms.push_back({std::string(varName), mpq_class(term.coefficient)});
        } else {
            return std::nullopt; // Non-linear
        }
    }

    std::sort(lhs.terms.begin(), lhs.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });
    return std::make_pair(lhs, rhs);
}

} // anonymous namespace

// Check whether a single linear/polynomial assignment satisfies all constraints
// using a fresh GeneralSimplex instance. Returns true iff SAT.
bool NiraSolver::checkAssignmentWithSimplex(
    const std::vector<ActiveAssignment>& activeAssignments,
    const std::unordered_map<std::string, mpq_class>& fixedValues,
    PolynomialKernel* kernel) {

    GeneralSimplex gs;
    LinearAtomManager manager;

    // Helper to assert bounds on an aux var
    auto assertRel = [&](int aux, Relation rel) -> bool {
        switch (rel) {
            case Relation::Eq:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)))) &&
                       gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Leq:
                return gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Lt:
                return gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0, -1))));
            case Relation::Geq:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Gt:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0, 1))));
            default:
                return true; // Neq not handled here
        }
    };

    // Process linear constraints (substitute fixed integer values)
    for (const auto& a : activeAssignments) {
        if (!a.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);

        LinearFormKey newLhs;
        mpq_class newRhs = p.rhs;
        for (const auto& [name, coeff] : p.lhs.terms) {
            auto it = fixedValues.find(name);
            if (it != fixedValues.end()) {
                newRhs -= it->second * coeff;
            } else {
                newLhs.terms.push_back({name, coeff});
            }
        }

        if (newLhs.terms.empty()) {
            bool sat = false;
            switch (p.rel) {
                case Relation::Eq:  sat = (newRhs == 0); break;
                case Relation::Neq: sat = (newRhs != 0); break;
                case Relation::Lt:  sat = (newRhs > 0); break;   // 0 < newRhs
                case Relation::Leq: sat = (newRhs >= 0); break;  // 0 <= newRhs
                case Relation::Gt:  sat = (newRhs < 0); break;   // 0 > newRhs
                case Relation::Geq: sat = (newRhs <= 0); break;  // 0 >= newRhs
            }
            if (!sat) return false;
            continue;
        }

        std::sort(newLhs.terms.begin(), newLhs.terms.end(),
                  [](auto& a, auto& b) { return a.first < b.first; });

        int aux = manager.getOrCreateAuxVar(gs, newLhs, newRhs);
        if (!assertRel(aux, p.rel)) return false;
    }

    // Process polynomial constraints (substitute fixed integer values)
    for (const auto& a : activeAssignments) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<PolynomialAtomPayload>(a.atom.payload);
        PolyId current = p.poly;

        for (const auto& [name, value] : fixedValues) {
            auto varIdOpt = kernel->findVar(name);
            if (!varIdOpt) continue;
            auto substituted = kernel->substituteRational(current, *varIdOpt, value);
            if (substituted) current = *substituted;
        }

        if (kernel->isConstant(current)) {
            mpq_class val = kernel->toConstant(current);
            bool sat = false;
            switch (p.rel) {
                case Relation::Eq:  sat = (val == 0); break;
                case Relation::Neq: sat = (val != 0); break;
                case Relation::Lt:  sat = (val < 0); break;
                case Relation::Leq: sat = (val <= 0); break;
                case Relation::Gt:  sat = (val > 0); break;
                case Relation::Geq: sat = (val >= 0); break;
            }
            if (!sat) return false;
            continue;
        }

        auto linearOpt = polyToLinearForm(kernel, current);
        if (!linearOpt) {
            return false;
        }

        auto [lhs, rhs] = *linearOpt;
        int aux = manager.getOrCreateAuxVar(gs, lhs, rhs);
        if (!assertRel(aux, p.rel)) return false;
    }

    auto r = gs.check();
    return r == GeneralSimplex::Result::Sat;
}

TheoryCheckResult NiraSolver::checkBoundedComplete(TheoryLemmaDatabase& /*lemmaDb*/) {
    if (!coreIr_ || !kernel_) {
        return TheoryCheckResult::unknown();
    }

    // Step 1: Extract integer variable bounds from single-variable linear constraints
    struct BoundInfo {
        std::optional<mpz_class> lower;
        std::optional<mpz_class> upper;
    };
    std::unordered_map<std::string, BoundInfo> bounds;

    for (const auto& a : activeAssignments_) {
        if (!a.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);
        if (p.lhs.terms.size() != 1) continue;

        const auto& [name, coeff] = p.lhs.terms[0];
        if (!isIntegerVar(coreIr_, name)) continue;

        mpq_class rawBound = p.rhs / coeff;
        if (rawBound.get_den() != 1) continue;

        mpz_class boundVal = rawBound.get_num();
        bool pos = coeff > 0;

        switch (p.rel) {
            case Relation::Eq:
                bounds[name].lower = boundVal;
                bounds[name].upper = boundVal;
                break;
            case Relation::Leq:
                if (pos) bounds[name].upper = boundVal;
                else     bounds[name].lower = boundVal;
                break;
            case Relation::Geq:
                if (pos) bounds[name].lower = boundVal;
                else     bounds[name].upper = boundVal;
                break;
            case Relation::Lt:
                if (pos) bounds[name].upper = boundVal - 1;
                else     bounds[name].lower = boundVal + 1;
                break;
            case Relation::Gt:
                if (pos) bounds[name].lower = boundVal + 1;
                else     bounds[name].upper = boundVal - 1;
                break;
            default: break;
        }
    }

    // Step 2: Identify integer variables appearing in polynomial constraints
    std::unordered_set<std::string> polyIntVars;
    for (const auto& a : activeAssignments_) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<PolynomialAtomPayload>(a.atom.payload);
        auto vars = kernel_->variables(p.poly);
        for (const auto& v : vars) {
            if (isIntegerVar(coreIr_, v)) polyIntVars.insert(v);
        }
    }

    if (polyIntVars.empty()) {
        return TheoryCheckResult::unknown();
    }

    // Step 3: Ensure every polynomial integer variable has finite bounds
    for (const auto& name : polyIntVars) {
        auto it = bounds.find(name);
        if (it == bounds.end() || !it->second.lower || !it->second.upper) {
            return TheoryCheckResult::unknown();
        }
    }

    // Step 4: Enumerate all integer combinations
    std::vector<std::string> enumVars(polyIntVars.begin(), polyIntVars.end());
    std::sort(enumVars.begin(), enumVars.end());
    std::unordered_map<std::string, mpq_class> fixedValues;

    std::function<bool(int)> enumerate = [&](int idx) -> bool {
        if (idx == (int)enumVars.size()) {
            return NiraSolver::checkAssignmentWithSimplex(activeAssignments_, fixedValues, kernel_.get());
        }

        const std::string& varName = enumVars[idx];
        mpz_class lo = *bounds[varName].lower;
        mpz_class hi = *bounds[varName].upper;

        if (lo > hi) return false;

        for (mpz_class val = lo; val <= hi; ++val) {
            fixedValues[varName] = mpq_class(val);
            if (enumerate(idx + 1)) return true;
        }
        fixedValues.erase(varName);
        return false;
    };

    if (enumerate(0)) {
        return TheoryCheckResult::consistent();
    }

    return TheoryCheckResult::unknown();
}

bool NiraSolver::validateOriginalConstraints() const {
    return true;
}

void NiraSolver::reset() {
    activeAssignments_.clear();
    gsRelax_.reset();
}

void NiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

void NiraSolver::setCoreIr(const CoreIr* ir) {
    coreIr_ = ir;
}

std::optional<TheorySolver::TheoryModel> NiraSolver::getModel() const {
    return std::nullopt;
}

std::vector<SatLit> NiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : activeAssignments_) {
        reasons.push_back(a.lit);
    }
    return reasons;
}

} // namespace nlcolver
