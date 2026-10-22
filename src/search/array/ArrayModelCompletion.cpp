#include "base/RuntimeConfig.h"
#include "search/array/ArrayModelCompletion.h"
#include "evidence/ArithModelValidator.h"
#include "base/EnvParam.h"
#include <iostream>
#include <map>
#include <set>

namespace xolver {
bool completeArrayModel(const NativeTerms& ir, const std::vector<ExprId>& roots,
                        TheorySolver::TheoryModel& model) {
    if (model.arrayInterps.empty() && model.arrayValues.empty()) return false;
    auto candidate = model;
    std::vector<TheoryModel::ArrayInterp*> arrays;
    for (auto& [name, value] : candidate.arrayInterps) arrays.push_back(&value);
    for (auto& [handle, value] : candidate.arrayValues) arrays.push_back(&value);
    if (config::read<config::ReadKind::Presence>("XOLVER_DIAG_AM")) {
        std::cerr << "[DIAG_AM] numeric assignments:";
        for (const auto& [name, number] : candidate.numericAssignments)
            if (auto q = number.tryAsRational()) std::cerr << ' ' << name << '=' << q->get_str();
        std::cerr << '\n';
    }
    std::map<std::string, std::string> aliases;
    auto resolve = [&](std::string value) {
        auto it = aliases.find(value);
        while (it != aliases.end()) { value = it->second; it = aliases.find(value); }
        return value;
    };
    auto opaque = [](const std::string& value) { return !value.empty() && value[0] == '@'; };
    auto unify = [&](std::string a, std::string b) {
        a = resolve(a); b = resolve(b);
        if (a == b) return true;
        if (!opaque(a) && !opaque(b)) return false;
        // Only opaque values are assignable. Numeric coincidences of different
        // e-classes are legal unless the actual formula requires disequality.
        if (!opaque(a) || (opaque(b) && a < b)) std::swap(a, b);
        aliases.emplace(a, b);
        return true;
    };
    // An equality between finite store chains also connects their base
    // defaults. EUF can choose either chain as a class representative and
    // leave the other base with a fresh default token. Reconcile those
    // assignable tokens before checking the original array equalities.
    // This only constructs a candidate; full validation below is mandatory.
    auto defaultOf = [&](ExprId id) -> std::optional<std::string> {
        while (id < ir.size()) {
            const auto& term = ir.get(id);
            if (term.kind == Kind::Store && term.children.size() == 3) {
                id = term.children[0];
                continue;
            }
            if (term.kind == Kind::Variable) {
                if (auto name = std::get_if<std::string>(&term.payload.value)) {
                    auto found = candidate.arrayInterps.find(*name);
                    if (found != candidate.arrayInterps.end()) return found->second.defaultVal;
                }
            }
            break;
        }
        return std::nullopt;
    };
    std::vector<ExprId> pending = roots;
    std::set<ExprId> visited;
    while (!pending.empty()) {
        const ExprId id = pending.back(); pending.pop_back();
        if (id >= ir.size() || !visited.insert(id).second) continue;
        const auto& term = ir.get(id);
        if (term.kind == Kind::And) {
            pending.insert(pending.end(), term.children.begin(), term.children.end());
            continue;
        }
        std::optional<ExprId> equality;
        if (term.kind == Kind::Eq && term.children.size() == 2) equality = id;
        // Binary not-distinct is equality too. For arity > 2 its negation
        // only requires some pair to coincide, so no particular pair may be
        // merged. Likewise do not infer equalities below arbitrary negation
        // or disjunction.
        if (term.kind == Kind::Not && term.children.size() == 1) {
            const auto& child = ir.get(term.children[0]);
            if (child.kind == Kind::Distinct && child.children.size() == 2)
                equality = term.children[0];
        }
        if (equality) {
            // get() returns a value. Retain a stable native ID across the
            // branch above, never a pointer to its block-local term view.
            const auto equalityTerm = ir.get(*equality);
            const auto left = defaultOf(equalityTerm.children[0]);
            const auto right = defaultOf(equalityTerm.children[1]);
            if (left && right && !unify(*left, *right)) return false;
        }
    }
    for (const auto& [name, number] : candidate.numericAssignments) {
        auto it = candidate.assignments.find(name);
        auto rational = number.tryAsRational();
        if (it != candidate.assignments.end() && opaque(it->second) && rational) {
            if (!unify(it->second, "#n:" + rational->get_str())) return false;
        }
    }
    // Generated reads can use different EUF index classes that the arithmetic
    // model assigns the same number. Their table entries must share one value.
    // Do not let unordered iteration silently overwrite a known read with an
    // unresolved token at that same concrete index.
    std::size_t before;
    do {
        before = aliases.size();
        for (const auto* arrayPtr : arrays) {
            const auto& array = *arrayPtr;
            std::map<std::string, std::string> reads;
            for (const auto& [index, element] : array.entries) {
                auto [it, fresh] = reads.emplace(resolve(index), resolve(element));
                if (!fresh && !unify(it->second, element)) {
                    // A numeric collision may invalidate an inherited table
                    // entry after stores have overwritten it. Keep a candidate
                    // last write; only full original-formula validation below
                    // can authorize adopting this interpretation.
                    it->second = resolve(element);
                }
            }
        }
    } while (aliases.size() != before);

    std::set<mpq_class> used;
    auto note = [&](const std::string& token) {
        const auto value = resolve(token);
        if (value.rfind("#n:", 0) == 0) {
            mpq_class q(value.substr(3)); q.canonicalize(); used.insert(q);
        }
    };
    std::set<std::string> numericTokens;
    auto needNumber = [&](const std::string& token) {
        note(token);
        auto value = resolve(token);
        if (opaque(value)) numericTokens.insert(value);
    };
    for (const auto* arrayPtr : arrays) {
            const auto& array = *arrayPtr;
        const bool numericIndex = array.indexSort == "Int" || array.indexSort == "Real";
        const bool numericElement = array.elemSort == "Int" || array.elemSort == "Real";
        if (numericElement) needNumber(array.defaultVal);
        for (const auto& [index, element] : array.entries) {
            if (numericIndex) needNumber(index);
            if (numericElement) needNumber(element);
        }
    }
    for (const auto& [name, number] : candidate.numericAssignments)
        if (auto q = number.tryAsRational()) used.insert(*q);
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        auto sk = ir.sortKind(e.sort);
        if (e.kind != Kind::Variable || (sk != SortKind::Int && sk != SortKind::Real)) continue;
        auto name = std::get_if<std::string>(&e.payload.value);
        if (!name) continue;
        auto it = candidate.assignments.find(*name);
        if (it != candidate.assignments.end()) needNumber(it->second);
    }
    mpz_class next = 0;
    for (const auto& token : numericTokens) {
        while (used.count(mpq_class(next))) ++next;
        aliases.emplace(token, "#n:" + next.get_str());
        used.insert(mpq_class(next));
        ++next;
    }
    for (auto& [name, token] : candidate.assignments) token = resolve(token);
    for (auto* arrayPtr : arrays) {
        auto& array = *arrayPtr;
        array.defaultVal = resolve(array.defaultVal);
        std::map<std::string, std::string> reads;
        for (const auto& [index, element] : array.entries) {
            const auto value = resolve(element);
            auto [it, fresh] = reads.emplace(resolve(index), value);
            if (!fresh) it->second = value;
        }
        array.entries.assign(reads.begin(), reads.end());
        auto typedNumber = [](const std::string& sort, const std::string& value) {
            if (sort != "Int" && sort != "Real") return true;
            if (value.rfind("#n:", 0) != 0) return false;
            mpq_class q(value.substr(3)); q.canonicalize();
            return sort != "Int" || q.get_den() == 1;
        };
        if (!typedNumber(array.elemSort, array.defaultVal)) return false;
        for (const auto& [index, element] : array.entries)
            if (!typedNumber(array.indexSort, index) || !typedNumber(array.elemSort, element))
                return false;
    }
    auto functionToken = [&](std::string value) {
        value = resolve(value);
        if (value.rfind("#n:", 0) == 0) return value.substr(3);
        if (value == "#b:1") return std::string("true");
        if (value == "#b:0") return std::string("false");
        return value;
    };
    for (auto& [name, function] : candidate.functionInterps) {
        function.deflt = functionToken(function.deflt);
        std::map<std::vector<std::string>, std::string> values;
        for (auto& entry : function.entries) {
            for (auto& arg : entry.args) arg = functionToken(arg);
            entry.value = functionToken(entry.value);
            auto [it, fresh] = values.emplace(entry.args, entry.value);
            if (!fresh && it->second != entry.value) return false;
        }
        // A constant interpretation extends a table whose observed outputs
        // all coincide. It also provides a concrete model for array-valued UF
        // arguments without relying on opaque e-class identity for arrays.
        if (!function.entries.empty() &&
            (function.retSort == "Int" || function.retSort == "Real" || function.retSort == "Bool")) {
            const auto value = function.entries.front().value;
            bool constant = !value.empty() && !opaque(value) &&
                            (function.deflt.empty() || function.deflt == value);
            for (const auto& entry : function.entries) constant &= entry.value == value;
            if (constant) { function.deflt = value; function.entries.clear(); }
        }
        // The table constrains only finitely many argument tuples. Any observed
        // output extends it to a total function outside those tuples.
        if (function.deflt.empty() && !function.entries.empty()) {
            function.deflt = function.entries.front().value;
        }
    }
    ArithModelValidator::NumAssignment numbers;
    ArithModelValidator::BoolAssignment booleans;
    for (const auto& [name, value] : candidate.assignments) {
        if (value == "true" || value == "false") booleans[name] = value == "true";
        else if (value.rfind("#n:", 0) == 0) {
            mpq_class q(value.substr(3)); q.canonicalize();
            numbers[name] = q;
            candidate.numericAssignments[name] = RealValue::fromMpq(q);
        } else if (!opaque(value)) {
            try { numbers[name] = mpq_class(value); } catch (...) {}
        }
    }
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind != Kind::Variable || ir.sortKind(e.sort) != SortKind::Int) continue;
        auto name = std::get_if<std::string>(&e.payload.value);
        if (name && numbers.count(*name) && numbers.at(*name).get_den() != 1) return false;
    }
    ArithModelValidator validator(ir, numbers, booleans, candidate.arrayInterps, candidate.assignments);
    validator.setFunctionInterps(&candidate.functionInterps, &candidate.arrayValues);
    if (validator.validate(roots) != ArithModelValidator::Verdict::Satisfied) {
        if (config::read<config::ReadKind::Presence>("XOLVER_DIAG_AM")) {
            for (std::size_t i = 0; i < roots.size(); ++i)
                std::cerr << "[DIAG_AM] completion assertion " << i << ": "
                          << static_cast<int>(validator.validate({roots[i]})) << '\n';
        }
        return false;
    }
    model = std::move(candidate);
    return true;
}
}
