#include "expr/Smt2Dumper.h"
#include <sstream>
#include <unordered_set>
#include <gmpxx.h>

namespace {
// Print a rational value string ("2", "-3", "1/3") as a valid SMT-LIB Real literal
// (N.0 or (/ N.0 D.0)) so it parses in a Real-sorted context — e.g. RDL's
// (* 2 x) with x:Real, where a bare "2" is an Int numeral and a strict checker
// (Carcara) rejects the Int/Real mix.
std::string realLiteral(const std::string& v) {
    mpq_class q(v);
    q.canonicalize();
    auto dec = [](mpz_class n) { return n.get_str() + ".0"; };
    if (q.get_den() == 1) {
        if (q.get_num() < 0) return "(- " + dec(-q.get_num()) + ")";
        return dec(q.get_num());
    }
    if (q.get_num() < 0)
        return "(- (/ " + dec(-q.get_num()) + " " + dec(q.get_den()) + "))";
    return "(/ " + dec(q.get_num()) + " " + dec(q.get_den()) + ")";
}
}  // namespace

namespace xolver {

static const char* kindToSMT2(Kind k) {
    switch (k) {
        case Kind::Not:       return "not";
        case Kind::And:       return "and";
        case Kind::Or:        return "or";
        case Kind::Implies:   return "=>";
        case Kind::Xor:       return "xor";
        case Kind::Ite:       return "ite";
        case Kind::Add:       return "+";
        case Kind::Sub:       return "-";
        case Kind::Neg:       return "-";
        case Kind::Mul:       return "*";
        case Kind::Div:       return "div";
        case Kind::Mod:       return "mod";
        case Kind::Abs:       return "abs";
        case Kind::Pow:       return "^";
        case Kind::Eq:        return "=";
        case Kind::Distinct:  return "distinct";
        case Kind::Lt:        return "<";
        case Kind::Leq:       return "<=";
        case Kind::Gt:        return ">";
        case Kind::Geq:       return ">=";
        case Kind::BvNot:     return "bvnot";
        case Kind::BvAnd:     return "bvand";
        case Kind::BvOr:      return "bvor";
        case Kind::BvAdd:     return "bvadd";
        case Kind::BvMul:     return "bvmul";
        case Kind::Forall:    return "forall";
        case Kind::Exists:    return "exists";
        case Kind::ToInt:     return "to_int";
        case Kind::ToReal:    return "to_real";
        case Kind::IsInt:     return "is_int";
        default:              return "";
    }
}

static void dumpRec(ExprId root, const CoreIr& ir, std::ostream& os, int /*depth*/ = 0) {
    // Iterative emit (was recursive on children; a deeply-nested term overflowed
    // the stack — the former depth>100000 guard sat far above the 8MB limit).
    // A work item is either a literal to emit (lit != nullptr) or a node to
    // expand. Children are pushed in reverse with interleaved " " separators so
    // output order matches the recursive "(op c0 c1 ... )".
    struct Item { ExprId id; const char* lit; };
    std::vector<Item> stack;
    stack.push_back({root, nullptr});

    while (!stack.empty()) {
        Item it = stack.back();
        stack.pop_back();
        if (it.lit) { os << it.lit; continue; }

        ExprId id = it.id;
        if (id >= ir.size()) { os << "???"; continue; }
        const auto& e = ir.get(id);

        auto expandChildren = [&]() {
            stack.push_back({NullExpr, ")"});
            for (size_t i = e.children.size(); i-- > 0;) {
                stack.push_back({e.children[i], nullptr});
                stack.push_back({NullExpr, " "});
            }
        };

        switch (e.kind) {
            case Kind::ConstBool:
                os << (std::get<bool>(e.payload.value) ? "true" : "false");
                break;
            case Kind::ConstInt:
                // A Real-sorted integer literal must print as "N.0" (e.g. RDL),
                // an Int-sorted one stays bare (e.g. IDL).
                if (ir.sortKind(e.sort) == SortKind::Real)
                    os << realLiteral(std::to_string(std::get<int64_t>(e.payload.value)));
                else
                    os << std::get<int64_t>(e.payload.value);
                break;
            case Kind::ConstReal:
                os << realLiteral(std::get<std::string>(e.payload.value));
                break;
            case Kind::ConstBV:
                if (std::holds_alternative<uint64_t>(e.payload.value)) {
                    os << "#b" << std::get<uint64_t>(e.payload.value);
                } else {
                    os << std::get<std::string>(e.payload.value);
                }
                break;
            case Kind::ConstFP:
                os << std::get<std::string>(e.payload.value);
                break;
            case Kind::Variable:
                os << std::get<std::string>(e.payload.value);
                break;
            case Kind::UFApply:
                os << "(" << std::get<std::string>(e.payload.value);
                expandChildren();
                break;
            case Kind::Unknown:
                os << "???";
                break;
            case Kind::Div: {
                // The IR uses one Div kind for both; real division prints as "/",
                // integer division as "div" — disambiguate by the result sort
                // (kindToSMT2 has no sort context and would always say "div").
                auto sk = ir.sortKind(e.sort);
                os << "(" << (sk && *sk == SortKind::Real ? "/" : "div");
                expandChildren();
                break;
            }
            default: {
                const char* op = kindToSMT2(e.kind);
                if (!op || !*op) {
                    os << "???";
                } else {
                    os << "(" << op;
                    expandChildren();
                }
                break;
            }
        }
    }
}

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir) {
    std::ostringstream oss;
    dumpRec(id, ir, oss);
    return oss.str();
}

namespace {
// Depth-first collect of the free Variables under `id`, in first-seen order.
void collectVars(ExprId id, const CoreIr& ir, std::vector<ExprId>& out,
                 std::unordered_set<ExprId>& seenVar,
                 std::unordered_set<ExprId>& visited) {
    if (id == NullExpr || id >= ir.size() || !visited.insert(id).second) return;
    const auto& e = ir.get(id);
    if (e.kind == Kind::Variable) {
        if (seenVar.insert(id).second) out.push_back(id);
        return;
    }
    for (ExprId c : e.children) collectVars(c, ir, out, seenVar, visited);
}

const char* sortToSMT2(const CoreIr& ir, SortId s) {
    auto sk = ir.sortKind(s);
    if (!sk) return "Real";
    switch (*sk) {
        case SortKind::Bool: return "Bool";
        case SortKind::Int:  return "Int";
        case SortKind::Real: return "Real";
        default:             return "Real";  // LRA/LIA first; widen later
    }
}
} // namespace

std::string dumpProblemToSMT2(const CoreIr& ir, const std::vector<ExprId>& assertions) {
    std::vector<ExprId> vars;
    std::unordered_set<ExprId> seenVar, visited;
    for (ExprId a : assertions) collectVars(a, ir, vars, seenVar, visited);

    std::ostringstream os;
    os << "(set-logic ALL)\n";
    for (ExprId v : vars)
        os << "(declare-const "
           << std::get<std::string>(ir.get(v).payload.value) << ' '
           << sortToSMT2(ir, ir.get(v).sort) << ")\n";
    for (ExprId a : assertions)
        os << "(assert " << dumpExprToSMT2(a, ir) << ")\n";
    os << "(check-sat)\n";
    return os.str();
}

} // namespace xolver
