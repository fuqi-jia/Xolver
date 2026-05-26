#include "frontend/preprocess/ModelConverter.h"
#include "util/MpqUtils.h"
#include <gmpxx.h>

namespace zolver {

void ModelConverter::registerElimination(std::string name, SortId sort, ExprId definingExpr) {
    elims_.push_back({std::move(name), sort, definingExpr});
}

std::optional<mpq_class> ModelConverter::evalRational(
    ExprId root, const CoreIr& ir,
    const std::unordered_map<std::string, mpq_class>& env) {
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
                    if (it == env.end()) return std::nullopt;  // unknown var
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
    env.reserve(numAsg.size() + strAsg.size() + elims_.size());
    for (const auto& [name, rv] : numAsg) {
        if (auto q = rv.tryAsRational()) env.emplace(name, *q);
    }
    for (const auto& [name, s] : strAsg) {
        if (env.count(name)) continue;
        if (s == "true" || s == "false") continue;
        try { env.emplace(name, mpqFromString(s)); } catch (...) {}
    }

    bool allOk = true;
    // Newest elimination first: a term may reference a later-eliminated var.
    for (auto it = elims_.rbegin(); it != elims_.rend(); ++it) {
        auto v = evalRational(it->expr, ir, env);
        if (!v) { allOk = false; continue; }
        numAsg[it->name] = RealValue::fromMpq(*v);
        strAsg[it->name] = v->get_str();   // bare mpq form: "5", "3/2", "-7/2"
        env[it->name] = *v;
    }
    return allOk;
}

} // namespace zolver
