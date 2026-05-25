#include "proof/ArithModelValidator.h"

namespace nlcolver {

ArithModelValidator::Verdict
ArithModelValidator::validate(const std::vector<ExprId>& assertions) const {
    bool anyIndeterminate = false;
    for (ExprId a : assertions) {
        TR r = eval(a);
        if (r.kind == Kind2::Indeterminate) { anyIndeterminate = true; continue; }
        if (r.kind != Kind2::Bool) { anyIndeterminate = true; continue; }
        if (!r.b) return Verdict::Violated;  // definite false
    }
    return anyIndeterminate ? Verdict::Indeterminate : Verdict::Satisfied;
}

ArithModelValidator::TR ArithModelValidator::eval(ExprId eid) const {
    if (eid >= ir_.size()) return {};
    const CoreExpr& n = ir_.get(eid);
    TR r;
    auto num = [](mpq_class v) { TR t; t.kind = Kind2::Number; t.n = std::move(v); return t; };
    auto bl  = [](bool v)      { TR t; t.kind = Kind2::Bool;   t.b = v; return t; };

    switch (n.kind) {
        case Kind::ConstBool:
            return bl(std::get<bool>(n.payload.value));
        case Kind::ConstInt:
            if (auto* v = std::get_if<int64_t>(&n.payload.value)) return num(mpq_class(*v));
            return r;
        case Kind::ConstReal:
            if (auto* s = std::get_if<std::string>(&n.payload.value)) return num(mpq_class(*s));
            return r;
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                if (n.sort == ir_.boolSortId()) {
                    auto it = boolAsg_.find(*s);
                    if (it != boolAsg_.end()) return bl(it->second);
                    return r;  // indeterminate
                }
                auto it = num_.find(*s);
                if (it != num_.end()) return num(it->second);
            }
            return r;
        }
        case Kind::Add: {
            mpq_class acc(0);
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Number) return r;
                acc += cr.n;
            }
            return num(acc);
        }
        case Kind::Sub: {
            if (n.children.empty()) return r;
            TR f = eval(n.children[0]);
            if (f.kind != Kind2::Number) return r;
            mpq_class acc = f.n;
            for (size_t i = 1; i < n.children.size(); ++i) {
                TR cr = eval(n.children[i]);
                if (cr.kind != Kind2::Number) return r;
                acc -= cr.n;
            }
            return num(acc);
        }
        case Kind::Neg: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return num(-cr.n);
        }
        case Kind::Mul: {
            mpq_class acc(1);
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Number) return r;
                acc *= cr.n;
            }
            return num(acc);
        }
        case Kind::Div: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Number || b.kind != Kind2::Number) return r;
            if (b.n == 0) return r;  // div/0 underspecified → indeterminate
            // SMT-LIB `div` on Int is EUCLIDEAN integer division (result in
            // Z, remainder 0 ≤ r < |b|); `/` on Real is rational division.
            // Distinguish by the node's sort.
            if (n.sort == ir_.intSortId()) {
                if (a.n.get_den() != 1 || b.n.get_den() != 1) return r;
                mpz_class ai = a.n.get_num(), bi = b.n.get_num();
                mpz_class absB = abs(bi), qAbs, rem;
                mpz_fdiv_qr(qAbs.get_mpz_t(), rem.get_mpz_t(),
                            ai.get_mpz_t(), absB.get_mpz_t());  // 0 ≤ rem < |b|
                mpz_class q = (bi > 0) ? qAbs : -qAbs;
                return num(mpq_class(q));
            }
            return num(a.n / b.n);
        }
        case Kind::Pow: {
            if (n.children.size() != 2) return r;
            TR base = eval(n.children[0]), exp = eval(n.children[1]);
            if (base.kind != Kind2::Number || exp.kind != Kind2::Number) return r;
            if (exp.n.get_den() != 1) return r;
            mpz_class e = exp.n.get_num();
            if (!e.fits_slong_p()) return r;
            long ev = e.get_si();
            if (ev < 0) { if (base.n == 0) return r; }
            mpq_class val(1);
            for (long i = 0; i < (ev < 0 ? -ev : ev); ++i) val *= base.n;
            if (ev < 0) return num(mpq_class(1) / val);
            return num(val);
        }
        case Kind::Abs: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return num(abs(cr.n));
        }
        case Kind::Mod: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Number || b.kind != Kind2::Number) return r;
            if (a.n.get_den() != 1 || b.n.get_den() != 1 || b.n == 0) return r;
            mpz_class ai = a.n.get_num(), bi = b.n.get_num(), absB = abs(bi), q, rem;
            mpz_fdiv_qr(q.get_mpz_t(), rem.get_mpz_t(), ai.get_mpz_t(), absB.get_mpz_t());
            return num(mpq_class(rem));
        }
        case Kind::ToReal: {
            if (n.children.size() != 1) return r;
            return eval(n.children[0]);
        }
        case Kind::ToInt: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            mpz_class q;
            mpz_fdiv_q(q.get_mpz_t(), cr.n.get_num().get_mpz_t(), cr.n.get_den().get_mpz_t());
            return num(mpq_class(q));
        }
        case Kind::IsInt: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return bl(cr.n.get_den() == 1);
        }
        case Kind::Eq: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind == Kind2::Indeterminate || b.kind == Kind2::Indeterminate) return r;
            if (a.kind != b.kind) return r;
            return bl(a.kind == Kind2::Bool ? (a.b == b.b) : (a.n == b.n));
        }
        case Kind::Distinct: {
            std::vector<TR> vals;
            vals.reserve(n.children.size());
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind == Kind2::Indeterminate) return r;
                vals.push_back(cr);
            }
            for (size_t i = 0; i < vals.size(); ++i)
                for (size_t j = i + 1; j < vals.size(); ++j) {
                    if (vals[i].kind != vals[j].kind) continue;
                    bool same = vals[i].kind == Kind2::Bool
                        ? (vals[i].b == vals[j].b) : (vals[i].n == vals[j].n);
                    if (same) return bl(false);
                }
            return bl(true);
        }
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Number || b.kind != Kind2::Number) return r;
            switch (n.kind) {
                case Kind::Lt:  return bl(a.n <  b.n);
                case Kind::Leq: return bl(a.n <= b.n);
                case Kind::Gt:  return bl(a.n >  b.n);
                default:        return bl(a.n >= b.n);
            }
        }
        case Kind::And: {
            bool ind = false;
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind == Kind2::Indeterminate) { ind = true; continue; }
                if (cr.kind != Kind2::Bool) return r;
                if (!cr.b) return bl(false);
            }
            return ind ? r : bl(true);
        }
        case Kind::Or: {
            bool ind = false;
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind == Kind2::Indeterminate) { ind = true; continue; }
                if (cr.kind != Kind2::Bool) return r;
                if (cr.b) return bl(true);
            }
            return ind ? r : bl(false);
        }
        case Kind::Not: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Bool) return r;
            return bl(!cr.b);
        }
        case Kind::Implies: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Bool || b.kind != Kind2::Bool) return r;
            return bl(!a.b || b.b);
        }
        case Kind::Xor: {
            bool acc = false, seen = false;
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Bool) return r;
                acc = seen ? (acc != cr.b) : cr.b;
                seen = true;
            }
            return seen ? bl(acc) : r;
        }
        case Kind::Ite: {
            if (n.children.size() != 3) return r;
            TR c = eval(n.children[0]);
            if (c.kind != Kind2::Bool) return r;
            return eval(c.b ? n.children[1] : n.children[2]);
        }
        default:
            return r;  // UFApply, quantifiers, BV/FP, … → indeterminate
    }
}

} // namespace nlcolver
