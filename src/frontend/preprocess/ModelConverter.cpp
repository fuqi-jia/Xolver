#include "frontend/preprocess/ModelConverter.h"
#include "algebra/linear/LinearExpr.h"
#include "base/MpqUtils.h"
#include <algorithm>
#include <unordered_set>
#include <gmpxx.h>

namespace xolver {

void ModelConverter::registerElimination(std::string name, SortId sort, ExprId definingExpr) {
    steps_.push_back({std::move(name), sort, definingExpr});
}

void ModelConverter::registerUnconstrainedParameters(
    const NativeTerms& ir, const std::vector<ExprId>& residualAssertions) {
    try {
        WorkBudget budget;
        auto variables = [&](const std::vector<ExprId>& roots) {
            std::unordered_set<std::string> names;
            std::unordered_set<ExprId> seen;
            std::vector<ExprId> pending = roots;
            while (!pending.empty()) {
                budget.tick();
                const auto id = pending.back(); pending.pop_back();
                if (!seen.insert(id).second) continue;
                const auto& node = ir.get(id);
                if (node.kind == Kind::Variable &&
                    (ir.sortKind(node.sort) == SortKind::Int || ir.sortKind(node.sort) == SortKind::Real)) {
                    if (const auto* name = std::get_if<std::string>(&node.payload.value)) names.insert(*name);
                }
                pending.insert(pending.end(), node.children.begin(), node.children.end());
            }
            return names;
        };
        // Finish the entire residual scan before declaring any variable free.
        auto constrained = variables(residualAssertions);
        std::vector<ExprId> definitions;
        for (const auto& step : steps_) {
            constrained.insert(step.name); // reconstructed by its recorded definition
            definitions.push_back(step.expr);
        }
        constrained.insert(unconstrainedParameters_.begin(), unconstrainedParameters_.end());
        auto dependencies = variables(definitions);
        std::vector<std::string> free;
        for (const auto& name : dependencies)
            if (!constrained.contains(name)) free.push_back(name);
        std::sort(free.begin(), free.end());
        unconstrainedParameters_.insert(unconstrainedParameters_.end(), free.begin(), free.end());
    } catch (const ResourceExhausted&) {
        // Incomplete occurrence information never licenses a default choice.
    }
}

std::optional<bool> ModelConverter::evalBool(
    ExprId root, const NativeTerms& ir,
    const std::unordered_map<std::string, bool>& boolEnv,
    const std::unordered_map<std::string, mpq_class>& env) {
    const SortId boolSort = ir.boolSortId();
    std::unordered_map<ExprId, bool> val;

    auto boolOperands = [&](const TermExpr& n) -> bool {
        return !n.children.empty() && ir.get(n.children[0]).sort == boolSort;
    };

    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (val.count(e)) { stack.pop_back(); continue; }
        const TermExpr node = ir.get(e);

        if (!frame.processed) {
            frame.processed = true;
            // Numeric relation / numeric (dis)equality: leaf, via evalRational.
            const bool numRel = (node.kind == Kind::Lt || node.kind == Kind::Leq ||
                                 node.kind == Kind::Gt || node.kind == Kind::Geq) ||
                                ((node.kind == Kind::Eq || node.kind == Kind::Distinct) &&
                                 node.children.size() == 2 && !boolOperands(node));
            if (numRel) {
                if (node.children.size() != 2) return std::nullopt;
                auto a = evalRational(node.children[0], ir, env);
                auto b = evalRational(node.children[1], ir, env);
                if (!a || !b) return std::nullopt;
                bool r;
                switch (node.kind) {
                    case Kind::Lt:  r = (*a <  *b); break;
                    case Kind::Leq: r = (*a <= *b); break;
                    case Kind::Gt:  r = (*a >  *b); break;
                    case Kind::Geq: r = (*a >= *b); break;
                    case Kind::Eq:  r = (*a == *b); break;
                    case Kind::Distinct: r = (*a != *b); break;
                    default: return std::nullopt;
                }
                val[e] = r; stack.pop_back(); continue;
            }
            if (node.kind == Kind::ConstBool) {
                auto* b = std::get_if<bool>(&node.payload.value);
                if (!b) return std::nullopt;
                val[e] = *b; stack.pop_back(); continue;
            }
            if (node.kind == Kind::Variable) {
                auto* nm = std::get_if<std::string>(&node.payload.value);
                if (!nm) return std::nullopt;
                auto it = boolEnv.find(*nm);
                val[e] = (it != boolEnv.end()) ? it->second : false;  // unconstrained -> false
                stack.pop_back(); continue;
            }
            switch (node.kind) {
                case Kind::Not: case Kind::And: case Kind::Or:
                case Kind::Implies: case Kind::Xor: case Kind::Ite:
                case Kind::Eq: case Kind::Distinct:  // (bool operands)
                    for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                        ExprId c = node.children[i];
                        if (!val.count(c)) stack.push_back({c, false});
                    }
                    continue;
                default:
                    return std::nullopt;  // UFApply/Select/... not bool-evaluable
            }
        }

        stack.pop_back();
        switch (node.kind) {
            case Kind::Not:
                if (node.children.size() != 1) return std::nullopt;
                val[e] = !val.at(node.children[0]); break;
            case Kind::And: { bool r = true;  for (ExprId c : node.children) r = r && val.at(c); val[e] = r; break; }
            case Kind::Or:  { bool r = false; for (ExprId c : node.children) r = r || val.at(c); val[e] = r; break; }
            case Kind::Implies:
                if (node.children.size() != 2) return std::nullopt;
                val[e] = (!val.at(node.children[0])) || val.at(node.children[1]); break;
            case Kind::Xor:
                if (node.children.size() != 2) return std::nullopt;
                val[e] = val.at(node.children[0]) != val.at(node.children[1]); break;
            case Kind::Ite:
                if (node.children.size() != 3) return std::nullopt;
                val[e] = val.at(node.children[0]) ? val.at(node.children[1]) : val.at(node.children[2]); break;
            case Kind::Eq: {  // bool operands: all equal
                bool r = true;
                for (size_t i = 1; i < node.children.size(); ++i)
                    r = r && (val.at(node.children[i]) == val.at(node.children[0]));
                val[e] = r; break;
            }
            case Kind::Distinct:  // bool: 2 args -> !=, >2 args can't be pairwise distinct
                val[e] = (node.children.size() == 2)
                             ? (val.at(node.children[0]) != val.at(node.children[1]))
                             : false;
                break;
            default: return std::nullopt;
        }
    }
    auto it = val.find(root);
    if (it == val.end()) return std::nullopt;
    return it->second;
}

std::optional<mpq_class> ModelConverter::evalRational(
    ExprId root, const NativeTerms& ir,
    const std::unordered_map<std::string, mpq_class>& env,
    const std::unordered_map<std::string, bool>* boolEnv) {
    std::unordered_map<ExprId, mpq_class> val;

    auto parseConst = [](const Payload& p) -> std::optional<mpq_class> {
        if (auto* iv = std::get_if<int64_t>(&p.value)) return mpq_class(*iv);
        if (auto* sv = std::get_if<std::string>(&p.value)) {
            try { return mpqFromString(*sv); } catch (...) { return std::nullopt; }
        }
        return std::nullopt;
    };

    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (val.count(e)) { stack.pop_back(); continue; }

        const TermExpr node = ir.get(e);

        if (!frame.processed) {
            frame.processed = true;
            switch (node.kind) {
                case Kind::Variable: {
                    auto* nm = std::get_if<std::string>(&node.payload.value);
                    if (!nm) return std::nullopt;
                    auto it = env.find(*nm);
                    if (it == env.end()) return std::nullopt;
                    val[e] = it->second;
                    stack.pop_back();
                    continue;
                }
                case Kind::ConstInt:
                case Kind::ConstReal: {
                    auto c = parseConst(node.payload);
                    if (!c) return std::nullopt;
                    val[e] = *c;
                    stack.pop_back();
                    continue;
                }
                case Kind::Ite: {
                    // LAZY: don't pre-evaluate both branches. Evaluate the
                    // cond first (via evalBool, which lives on its own
                    // boolEnv namespace), then push ONLY the chosen branch.
                    // The other branch's variables may be missing from env —
                    // ignoring it lets reconstruct succeed when the cond
                    // unambiguously selects the populated branch. Sound:
                    // SMT-LIB Int Ite evaluates only the taken branch; the
                    // untaken branch's value doesn't affect the Ite value.
                    if (node.children.size() != 3) return std::nullopt;
                    if (!boolEnv) return std::nullopt;
                    auto condVal = evalBool(node.children[0], ir, *boolEnv, env);
                    if (!condVal) return std::nullopt;
                    ExprId chosen = *condVal ? node.children[1] : node.children[2];
                    if (!val.count(chosen)) stack.push_back({chosen, false});
                    continue;  // post-visit will look up val.at(chosen)
                }
                default: break;
            }
            if (node.children.empty()) return std::nullopt;  // unknown leaf kind
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (!val.count(c)) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        switch (node.kind) {
            case Kind::Add: {
                mpq_class s = 0;
                for (ExprId c : node.children) s += val.at(c);
                val[e] = s;
                break;
            }
            case Kind::Sub: {
                if (node.children.empty()) return std::nullopt;
                mpq_class s = val.at(node.children[0]);
                for (size_t k = 1; k < node.children.size(); ++k) s -= val.at(node.children[k]);
                val[e] = s;
                break;
            }
            case Kind::Neg: {
                if (node.children.size() != 1) return std::nullopt;
                val[e] = -val.at(node.children[0]);
                break;
            }
            case Kind::Mul: {
                mpq_class p = 1;
                for (ExprId c : node.children) p *= val.at(c);
                val[e] = p;
                break;
            }
            case Kind::Div: {
                if (node.sort != ir.realSortId() || node.children.size() != 2)
                    return std::nullopt;
                const auto& divisor = ir.get(node.children[1]);
                if (divisor.kind != Kind::ConstInt && divisor.kind != Kind::ConstReal)
                    return std::nullopt;
                const auto& denominator = val.at(node.children[1]);
                if (denominator == 0) return std::nullopt;
                val[e] = val.at(node.children[0]) / denominator;
                break;
            }
            case Kind::ToReal: {
                if (node.children.size() != 1) return std::nullopt;
                val[e] = val.at(node.children[0]);
                break;
            }
            case Kind::ToInt: {
                if (node.children.size() != 1) return std::nullopt;
                const mpq_class& q = val.at(node.children[0]);
                mpz_class fl;
                mpz_fdiv_q(fl.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                val[e] = mpq_class(fl);
                break;
            }
            case Kind::Ite: {
                // Post-visit: lazy variant only pushed the CHOSEN branch in
                // pre-visit. Re-derive which branch was taken via evalBool
                // (cheap; cond is typically a constant or single Bool var).
                if (node.children.size() != 3) return std::nullopt;
                if (!boolEnv) return std::nullopt;
                auto condVal = evalBool(node.children[0], ir, *boolEnv, env);
                if (!condVal) return std::nullopt;
                ExprId chosen = *condVal ? node.children[1] : node.children[2];
                val[e] = val.at(chosen);
                break;
            }
            case Kind::Mod: {
                // SMT-LIB Int mod: result in [0, |y|). y must be a nonzero
                // integer for the result to be defined; treat y=0 as 0 here
                // (matches the existing ArithModelValidator default).
                if (node.children.size() != 2) return std::nullopt;
                const mpq_class& a = val.at(node.children[0]);
                const mpq_class& b = val.at(node.children[1]);
                if (a.get_den() != 1 || b.get_den() != 1) return std::nullopt;
                mpz_class ai = a.get_num(), bi = b.get_num();
                if (bi == 0) { val[e] = mpq_class(0); break; }
                mpz_class absB = (bi > 0) ? bi : -bi;
                mpz_class rem;
                mpz_fdiv_r(rem.get_mpz_t(), ai.get_mpz_t(), absB.get_mpz_t());
                val[e] = mpq_class(rem);
                break;
            }
            default:
                return std::nullopt;  // non-linear / unsupported -> cannot rebuild
        }
    }

    auto it = val.find(root);
    if (it == val.end()) return std::nullopt;
    return it->second;
}

bool ModelConverter::reconstruct(std::unordered_map<std::string, RealValue>& numAsg,
                                 std::unordered_map<std::string, std::string>& strAsg,
                                 const NativeTerms& ir) const {
    // Rational environment from the current (solver-produced + already
    // reconstructed) assignment. Prefer the typed channel; fall back to the
    // string channel for vars only present there. Algebraic dependencies use
    // exact affine replay below instead of being rounded to rationals.
    std::unordered_map<std::string, mpq_class> env;
    env.reserve(numAsg.size() + strAsg.size() + steps_.size());
    for (const auto& [name, rv] : numAsg) {
        if (auto q = rv.tryAsRational()) env.emplace(name, *q);
    }
    for (const auto& [name, s] : strAsg) {
        if (numAsg.count(name) || env.count(name)) continue;
        if (s == "true" || s == "false") continue;
        try { env.emplace(name, mpqFromString(s)); } catch (...) {}
    }
    for (const auto& name : unconstrainedParameters_) {
        if (numAsg.count(name) || strAsg.count(name)) continue;
        numAsg.emplace(name, RealValue::fromInt(0));
        strAsg.emplace(name, "0");
        env.emplace(name, 0);
    }

    // Boolean environment from the string channel (for bool-var reconstruction).
    std::unordered_map<std::string, bool> boolEnv;
    for (const auto& [name, s] : strAsg) {
        if (s == "true")  boolEnv.emplace(name, true);
        else if (s == "false") boolEnv.emplace(name, false);
    }

    bool allOk = true;
    auto evalAffine = [&](ExprId expr) -> std::optional<RealValue> {
        try {
            WorkBudget budget;
            std::unordered_map<std::string, mpq_class> coefficients;
            mpq_class constant = 0;
            if (!extractLinearExpr(expr, ir, coefficients, constant, mpq_class(1), &budget))
                return std::nullopt;
            std::vector<std::pair<std::string, mpq_class>> ordered(coefficients.begin(), coefficients.end());
            std::sort(ordered.begin(), ordered.end());
            RealValue value = RealValue::fromMpq(constant);
            for (const auto& [name, coefficient] : ordered) {
                budget.tick();
                const auto typed = numAsg.find(name);
                const auto rational = env.find(name);
                // Even a cancelled dependency must be present: preserve the
                // converter's strict missing-variable contract.
                if (typed == numAsg.end() && rational == env.end()) return std::nullopt;
                if (coefficient == 0) continue;
                const auto dependency = typed != numAsg.end()
                    ? typed->second : RealValue::fromMpq(rational->second);
                value = value + RealValue::fromMpq(coefficient) * dependency;
            }
            return value;
        } catch (const std::exception&) {
            // Unsupported algebraic operations or exhausted resources do not
            // license a guessed model value.
            return std::nullopt;
        }
    };
    auto evalPolynomial = [&](ExprId expr) -> std::optional<RealValue> {
        try {
            WorkBudget budget;
            std::unordered_map<ExprId, RealValue> values;
            std::vector<std::pair<ExprId, bool>> pending{{expr, false}};
            while (!pending.empty()) {
                budget.tick();
                const auto [id, processed] = pending.back();
                pending.pop_back();
                if (values.contains(id)) continue;
                const auto& node = ir.get(id);
                if (!processed) {
                    if (node.kind == Kind::Variable) {
                        const auto* name = std::get_if<std::string>(&node.payload.value);
                        if (!name) return std::nullopt;
                        const auto typed = numAsg.find(*name);
                        const auto rational = env.find(*name);
                        if (typed == numAsg.end() && rational == env.end()) return std::nullopt;
                        values.emplace(id, typed != numAsg.end()
                            ? typed->second : RealValue::fromMpq(rational->second));
                        continue;
                    }
                    if (node.kind == Kind::ConstInt || node.kind == Kind::ConstReal) {
                        if (const auto* number = std::get_if<int64_t>(&node.payload.value))
                            values.emplace(id, RealValue::fromInt(*number));
                        else if (const auto* number = std::get_if<std::string>(&node.payload.value))
                            values.emplace(id, RealValue::fromMpq(mpqFromString(*number)));
                        else return std::nullopt;
                        continue;
                    }
                    if (node.kind == Kind::Div) {
                        if (node.sort != ir.realSortId() || node.children.size() != 2)
                            return std::nullopt;
                        const auto kind = ir.get(node.children[1]).kind;
                        if (kind != Kind::ConstInt && kind != Kind::ConstReal) return std::nullopt;
                    } else if (node.kind != Kind::Add && node.kind != Kind::Sub && node.kind != Kind::Neg &&
                               node.kind != Kind::Mul && node.kind != Kind::ToReal) return std::nullopt;
                    pending.emplace_back(id, true);
                    for (const auto child : node.children) {
                        budget.tick();
                        if (!values.contains(child)) pending.emplace_back(child, false);
                    }
                    continue;
                }
                RealValue value = RealValue::fromInt(node.kind == Kind::Mul ? 1 : 0);
                if (node.kind == Kind::Neg || node.kind == Kind::ToReal) {
                    if (node.children.size() != 1) return std::nullopt;
                    value = values.at(node.children[0]);
                    if (node.kind == Kind::Neg) value = -value;
                } else if (node.kind == Kind::Div) {
                    const auto denominator = values.at(node.children[1]).tryAsRational();
                    if (!denominator || *denominator == 0) return std::nullopt;
                    value = values.at(node.children[0]) * RealValue::fromMpq(mpq_class(1) / *denominator);
                } else if (node.kind == Kind::Sub) {
                    if (node.children.empty()) return std::nullopt;
                    value = values.at(node.children[0]);
                    for (size_t child = 1; child < node.children.size(); ++child)
                        value = value - values.at(node.children[child]);
                } else {
                    for (const auto child : node.children)
                        value = node.kind == Kind::Mul ? value * values.at(child) : value + values.at(child);
                }
                values.emplace(id, std::move(value));
            }
            return values.at(expr);
        } catch (const std::exception&) {
            // A missing dependency, unsupported algebraic operation or exhausted
            // budget leaves reconstruction incomplete, never a guessed value.
            return std::nullopt;
        }
    };
    // Newest step first: a term may reference a later-eliminated variable.
    for (auto it = steps_.rbegin(); it != steps_.rend(); ++it) {
        auto vb = evalRational(it->expr, ir, env, &boolEnv);
        auto value = vb ? std::optional<RealValue>(RealValue::fromMpq(*vb)) : evalAffine(it->expr);
        if (!value) value = evalPolynomial(it->expr);
        if (!value || (ir.sortKind(it->sort) == SortKind::Int && !value->isExactInteger())) {
            allOk = false;
            continue;
        }
        if (auto rational = value->tryAsRational()) {
            strAsg[it->name] = rational->get_str(); // preserve legacy bare mpq form
            env[it->name] = *rational;
        } else {
            strAsg[it->name] = value->toSmtLib2();
            env.erase(it->name); // discard any pre-elimination default value
        }
        numAsg[it->name] = std::move(*value);
    }
    return allOk;
}

} // namespace xolver
