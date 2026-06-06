#include "frontend/preprocess/ModelConverter.h"
#include "util/MpqUtils.h"
#include <gmpxx.h>

namespace xolver {

void ModelConverter::registerElimination(std::string name, SortId sort, ExprId definingExpr) {
    steps_.push_back({StepKind::Elim, std::move(name), sort, definingExpr, Rel::Ge});
}

void ModelConverter::registerUncElimination(std::string name, SortId sort, ExprId definingExpr) {
    steps_.push_back({StepKind::UncElim, std::move(name), sort, definingExpr, Rel::Ge});
}

void ModelConverter::registerWitness(std::string name, SortId sort, Rel rel, ExprId boundExpr) {
    steps_.push_back({StepKind::Witness, std::move(name), sort, boundExpr, rel});
}

void ModelConverter::registerBoolElimination(std::string name, ExprId definingExpr) {
    steps_.push_back({StepKind::BoolElim, std::move(name), NullSort, definingExpr, Rel::Ge});
}

std::optional<bool> ModelConverter::evalBool(
    ExprId root, const CoreIr& ir,
    const std::unordered_map<std::string, bool>& boolEnv,
    const std::unordered_map<std::string, mpq_class>& env) {
    const SortId boolSort = ir.boolSortId();
    std::unordered_map<ExprId, bool> val;

    auto boolOperands = [&](const CoreExpr& n) -> bool {
        return !n.children.empty() && ir.get(n.children[0]).sort == boolSort;
    };

    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (val.count(e)) { stack.pop_back(); continue; }
        const CoreExpr node = ir.get(e);

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
    ExprId root, const CoreIr& ir,
    const std::unordered_map<std::string, mpq_class>& env,
    const std::unordered_map<std::string, bool>* boolEnv,
    bool permissiveMissingVar) {
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

        const CoreExpr node = ir.get(e);

        if (!frame.processed) {
            frame.processed = true;
            switch (node.kind) {
                case Kind::Variable: {
                    auto* nm = std::get_if<std::string>(&node.payload.value);
                    if (!nm) return std::nullopt;
                    auto it = env.find(*nm);
                    if (it == env.end()) {
                        if (!permissiveMissingVar) return std::nullopt;
                        // Permissive (UncElim / Witness): treat missing var
                        // as 0 — sound because by construction the variable
                        // was also dropped as unconstrained, so any value
                        // satisfies the post-elim formula.
                        val[e] = mpq_class(0);
                    } else {
                        val[e] = it->second;
                    }
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
                                 const CoreIr& ir) const {
    // Rational environment from the current (solver-produced + already
    // reconstructed) assignment. Prefer the typed channel; fall back to the
    // string channel for vars only present there. Algebraic values are not
    // usable by the linear evaluator and are simply absent from env.
    std::unordered_map<std::string, mpq_class> env;
    env.reserve(numAsg.size() + strAsg.size() + steps_.size());
    for (const auto& [name, rv] : numAsg) {
        if (auto q = rv.tryAsRational()) env.emplace(name, *q);
    }
    for (const auto& [name, s] : strAsg) {
        if (env.count(name)) continue;
        if (s == "true" || s == "false") continue;
        try { env.emplace(name, mpqFromString(s)); } catch (...) {}
    }

    // Boolean environment from the string channel (for bool-var reconstruction).
    std::unordered_map<std::string, bool> boolEnv;
    for (const auto& [name, s] : strAsg) {
        if (s == "true")  boolEnv.emplace(name, true);
        else if (s == "false") boolEnv.emplace(name, false);
    }

    bool allOk = true;
    // Newest step first: a term may reference a later-eliminated variable.
    for (auto it = steps_.rbegin(); it != steps_.rend(); ++it) {
        if (it->kind == StepKind::BoolElim) {
            auto bv = evalBool(it->expr, ir, boolEnv, env);
            if (!bv) { allOk = false; continue; }
            strAsg[it->name] = *bv ? "true" : "false";
            boolEnv[it->name] = *bv;
            continue;
        }

        // Elim: strict (any missing free var = solver bug).
        // UncElim / Witness: permissive (free vars in the bound that were
        // themselves dropped as unconstrained default to 0 — sound, any
        // value satisfies the post-elim formula).
        bool permissive = (it->kind == StepKind::UncElim ||
                           it->kind == StepKind::Witness);
        auto vb = evalRational(it->expr, ir, env, &boolEnv, permissive);
        if (!vb) { allOk = false; continue; }

        mpq_class value;
        if (it->kind == StepKind::Elim || it->kind == StepKind::UncElim) {
            value = *vb;                              // x == defining term
        } else {
            // Witness: pick any value satisfying  x ⋈ bound.  vt±1 satisfies the
            // strict relations for both Int (integral) and Real.
            switch (it->rel) {
                case Rel::Ge: value = *vb; break;          // x >= b   -> b
                case Rel::Le: value = *vb; break;          // x <= b   -> b
                case Rel::Gt: value = *vb + 1; break;      // x >  b   -> b+1
                case Rel::Lt: value = *vb - 1; break;      // x <  b   -> b-1
                case Rel::Ne: value = *vb + 1; break;      // x != b   -> b+1
            }
        }
        numAsg[it->name] = RealValue::fromMpq(value);
        strAsg[it->name] = value.get_str();           // bare mpq form
        env[it->name] = value;
    }
    return allOk;
}

} // namespace xolver
