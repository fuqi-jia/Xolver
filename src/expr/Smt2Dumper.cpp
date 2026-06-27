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
            case Kind::Distinct:
                // Binary distinct IS sugar for (not (= a b)); render it that way so
                // a Carcara `resolution` step can cancel it against the (= a b) an
                // eq_transitive conclusion produces (Carcara does not desugar a bare
                // `distinct` into a negated equality during resolution). The proof's
                // assume and this problem assertion go through the SAME function, so
                // they stay textually identical. N-ary distinct (>2) is already
                // lowered to pairwise binary by NaryDistinctLowerer, but keep a
                // faithful `(distinct ...)` for any that survives.
                if (e.children.size() == 2) {
                    os << "(not (=";
                    stack.push_back({NullExpr, "))"});
                    for (size_t i = e.children.size(); i-- > 0;) {
                        stack.push_back({e.children[i], nullptr});
                        stack.push_back({NullExpr, " "});
                    }
                } else {
                    os << "(distinct";
                    expandChildren();
                }
                break;
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
// Everything a self-contained SMT-LIB problem must declare before its asserts:
// the free 0-ary symbols (Variables), the uninterpreted function symbols (with
// signatures), and the uninterpreted sorts they range over. Collected in
// first-seen order so the output is deterministic.
struct ProblemDecls {
    std::vector<ExprId> vars;                 // 0-ary symbols, declare-const
    std::unordered_set<ExprId> seenVar;
    std::vector<std::string> ufOrder;         // UF names, first-seen
    std::unordered_map<std::string, std::pair<std::vector<SortId>, SortId>> ufSig;
    std::vector<SortId> sorts;                // uninterpreted (Other) sorts, first-seen
    std::unordered_set<SortId> seenSort;
    std::unordered_set<ExprId> visited;
};

// Record an uninterpreted (SortKind::Other) sort the moment it is referenced, so
// every declare-const / declare-fun can name a sort that has its own declare-sort.
void noteSort(const CoreIr& ir, SortId s, ProblemDecls& d) {
    if (s == NullSort) return;
    auto sk = ir.sortKind(s);
    if (sk && *sk == SortKind::Other && d.seenSort.insert(s).second)
        d.sorts.push_back(s);
}

void collectDecls(ExprId id, const CoreIr& ir, ProblemDecls& d) {
    if (id == NullExpr || id >= ir.size() || !d.visited.insert(id).second) return;
    const auto& e = ir.get(id);
    if (e.kind == Kind::Variable) {
        noteSort(ir, e.sort, d);
        if (d.seenVar.insert(id).second) d.vars.push_back(id);
        return;
    }
    if (e.kind == Kind::UFApply) {
        const auto& name = std::get<std::string>(e.payload.value);
        if (d.ufSig.find(name) == d.ufSig.end()) {
            std::vector<SortId> dom;
            dom.reserve(e.children.size());
            for (ExprId c : e.children) dom.push_back(ir.get(c).sort);
            d.ufSig.emplace(name, std::make_pair(std::move(dom), e.sort));
            d.ufOrder.push_back(name);
            for (ExprId c : e.children) noteSort(ir, ir.get(c).sort, d);
            noteSort(ir, e.sort, d);
        }
    }
    for (ExprId c : e.children) collectDecls(c, ir, d);
}

// A stable SMT-LIB name for an uninterpreted sort. The IR carries no sort name
// (only a SortId + kind), and the proof is checked against THIS dumped problem
// (terms match by construction), so a synthesized name is sound: the first
// uninterpreted sort is "U" (the SMT-LIB convention) and any further ones get a
// numeric suffix.
std::string uninterpretedSortName(const std::vector<SortId>& sorts, SortId s) {
    for (size_t i = 0; i < sorts.size(); ++i)
        if (sorts[i] == s) return i == 0 ? "U" : "U" + std::to_string(i);
    return "U";  // unreachable: every Other sort was noteSort'd
}

std::string sortToSMT2(const CoreIr& ir, SortId s, const ProblemDecls& d) {
    auto sk = ir.sortKind(s);
    if (!sk) return "Real";
    switch (*sk) {
        case SortKind::Bool:  return "Bool";
        case SortKind::Int:   return "Int";
        case SortKind::Real:  return "Real";
        case SortKind::Other: return uninterpretedSortName(d.sorts, s);
        default:              return "Real";  // BV/FP/Array/Datatype: out of proof scope
    }
}
} // namespace

std::string dumpProblemToSMT2(const CoreIr& ir, const std::vector<ExprId>& assertions) {
    ProblemDecls d;
    for (ExprId a : assertions) collectDecls(a, ir, d);

    std::ostringstream os;
    os << "(set-logic ALL)\n";
    // Sorts first — a declare-fun / declare-const may name them.
    for (SortId s : d.sorts)
        os << "(declare-sort " << uninterpretedSortName(d.sorts, s) << " 0)\n";
    // Uninterpreted functions (declare-fun name (dom...) range).
    for (const std::string& name : d.ufOrder) {
        const auto& [dom, range] = d.ufSig.at(name);
        os << "(declare-fun " << name << " (";
        for (size_t i = 0; i < dom.size(); ++i)
            os << (i ? " " : "") << sortToSMT2(ir, dom[i], d);
        os << ") " << sortToSMT2(ir, range, d) << ")\n";
    }
    // 0-ary symbols.
    for (ExprId v : d.vars)
        os << "(declare-const "
           << std::get<std::string>(ir.get(v).payload.value) << ' '
           << sortToSMT2(ir, ir.get(v).sort, d) << ")\n";
    for (ExprId a : assertions)
        os << "(assert " << dumpExprToSMT2(a, ir) << ")\n";
    os << "(check-sat)\n";
    return os.str();
}

} // namespace xolver
