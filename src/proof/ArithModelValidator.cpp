#include "proof/ArithModelValidator.h"

namespace zolver {

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

std::optional<mpq_class> ArithModelValidator::evalNumber(ExprId e) const {
    TR r = eval(e);
    if (r.kind == Kind2::Number) return r.n.tryAsRational();  // algebraic → nullopt
    return std::nullopt;
}

// Coerce a value into a canonical equality token. Numbers and bools are given
// disjoint namespaces so they never alias an uninterpreted token by accident.
std::optional<std::string> ArithModelValidator::asToken(const TR& r) const {
    switch (r.kind) {
        case Kind2::Number:
            // Rational → canonical token; algebraic has no rational token here
            // (it cannot appear as an array index/element in practice).
            if (auto q = r.n.tryAsRational()) return "#n:" + q->get_str();
            return std::nullopt;
        case Kind2::Bool:   return std::string("#b:") + (r.b ? "1" : "0");
        case Kind2::Token:  return r.tok;
        default:            return std::nullopt;
    }
}

ArithModelValidator::TR ArithModelValidator::eval(ExprId eid) const {
    if (eid >= ir_.size()) return {};
    const CoreExpr& n = ir_.get(eid);
    TR r;
    auto num = [](RealValue v) { TR t; t.kind = Kind2::Number; t.n = std::move(v); return t; };
    auto bl  = [](bool v)      { TR t; t.kind = Kind2::Bool;   t.b = v; return t; };

    switch (n.kind) {
        case Kind::ConstBool:
            return bl(std::get<bool>(n.payload.value));
        case Kind::ConstInt:
            if (auto* v = std::get_if<int64_t>(&n.payload.value)) return num(RealValue::fromInt(*v));
            return r;
        case Kind::ConstReal:
            if (auto* s = std::get_if<std::string>(&n.payload.value)) return num(RealValue::fromMpq(mpq_class(*s)));
            return r;
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                // Array-sorted variable → look up its interpretation.
                if (arr_ && ir_.arraySortParams(n.sort)) {
                    auto it = arr_->find(*s);
                    if (it == arr_->end()) return r;  // indeterminate
                    TR t; t.kind = Kind2::Array;
                    t.arr.deflt = it->second.defaultVal;
                    for (const auto& [idx, val] : it->second.entries) {
                        t.arr.overrides[idx] = val;
                    }
                    return t;
                }
                // Boolean variable: identified by boolSortId, by the registered
                // sort-kind (boolSortId is unset on file-parsed IR, so the
                // sort-kind check is the reliable signal), or by a boolean
                // assignment carrying its value. A bool var with no assignment
                // stays Indeterminate.
                bool boolVar = (n.sort == ir_.boolSortId());
                if (!boolVar) {
                    auto sk = ir_.sortKind(n.sort);
                    if (sk && *sk == SortKind::Bool) boolVar = true;
                }
                auto bit = boolAsg_.find(*s);
                if (boolVar || bit != boolAsg_.end()) {
                    if (bit != boolAsg_.end()) return bl(bit->second);
                    return r;  // bool var, unassigned -> indeterminate
                }
                // Prefer the exact typed channel (real-algebraic witnesses),
                // then the rational channel.
                if (real_) {
                    auto rit = real_->find(*s);
                    if (rit != real_->end()) return num(rit->second);
                }
                auto it = num_.find(*s);
                if (it != num_.end()) return num(RealValue::fromMpq(it->second));
                // Uninterpreted-sort scalar (index/element): opaque token.
                if (tok_) {
                    auto tit = tok_->find(*s);
                    if (tit != tok_->end()) {
                        TR t; t.kind = Kind2::Token; t.tok = tit->second; return t;
                    }
                }
            }
            return r;
        }
        case Kind::Add: {
            RealValue acc;  // 0
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Number) return r;
                acc = acc + cr.n;
            }
            return num(acc);
        }
        case Kind::Sub: {
            if (n.children.empty()) return r;
            TR f = eval(n.children[0]);
            if (f.kind != Kind2::Number) return r;
            RealValue acc = f.n;
            for (size_t i = 1; i < n.children.size(); ++i) {
                TR cr = eval(n.children[i]);
                if (cr.kind != Kind2::Number) return r;
                acc = acc - cr.n;
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
            RealValue acc = RealValue::fromInt(1);
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Number) return r;
                acc = acc * cr.n;
            }
            return num(acc);
        }
        case Kind::Div: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Number || b.kind != Kind2::Number) return r;
            if (b.n.isZero()) return r;  // div/0 underspecified → indeterminate
            // SMT-LIB `div` on Int is EUCLIDEAN integer division; `/` on Real is
            // real division. Distinguish by the node's sort.
            if (n.sort == ir_.intSortId()) {
                if (!a.n.isExactInteger() || !b.n.isExactInteger()) return r;
                mpz_class ai = a.n.floor(), bi = b.n.floor();
                mpz_class absB = abs(bi), qAbs, rem;
                mpz_fdiv_qr(qAbs.get_mpz_t(), rem.get_mpz_t(),
                            ai.get_mpz_t(), absB.get_mpz_t());  // 0 ≤ rem < |b|
                mpz_class q = (bi > 0) ? qAbs : -qAbs;
                return num(RealValue::fromMpz(q));
            }
            return num(a.n / b.n);
        }
        case Kind::Pow: {
            if (n.children.size() != 2) return r;
            TR base = eval(n.children[0]), exp = eval(n.children[1]);
            if (base.kind != Kind2::Number || exp.kind != Kind2::Number) return r;
            if (!exp.n.isExactInteger()) return r;
            mpz_class e = exp.n.floor();
            if (!e.fits_slong_p()) return r;
            long ev = e.get_si();
            if (ev < 0 && base.n.isZero()) return r;
            RealValue val = RealValue::fromInt(1);
            for (long i = 0; i < (ev < 0 ? -ev : ev); ++i) val = val * base.n;
            if (ev < 0) return num(RealValue::fromInt(1) / val);
            return num(val);
        }
        case Kind::Abs: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return num(cr.n.sign() < 0 ? -cr.n : cr.n);
        }
        case Kind::Mod: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind != Kind2::Number || b.kind != Kind2::Number) return r;
            if (!a.n.isExactInteger() || !b.n.isExactInteger() || b.n.isZero()) return r;
            mpz_class ai = a.n.floor(), bi = b.n.floor(), absB = abs(bi), q, rem;
            mpz_fdiv_qr(q.get_mpz_t(), rem.get_mpz_t(), ai.get_mpz_t(), absB.get_mpz_t());
            return num(RealValue::fromMpz(rem));
        }
        case Kind::ToReal: {
            if (n.children.size() != 1) return r;
            return eval(n.children[0]);
        }
        case Kind::ToInt: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return num(RealValue::fromMpz(cr.n.floor()));  // floor (Euclidean)
        }
        case Kind::IsInt: {
            if (n.children.size() != 1) return r;
            TR cr = eval(n.children[0]);
            if (cr.kind != Kind2::Number) return r;
            return bl(cr.n.isExactInteger());
        }
        case Kind::Eq: {
            if (n.children.size() != 2) return r;
            TR a = eval(n.children[0]), b = eval(n.children[1]);
            if (a.kind == Kind2::Indeterminate || b.kind == Kind2::Indeterminate) return r;
            // Array equality: equal defaults AND equal at every read index of
            // the union. a != b iff some explicit read index differs (no
            // default-distinctness shortcut: if defaults differ but no read
            // witnesses it, that alone does NOT prove inequality here).
            if (a.kind == Kind2::Array && b.kind == Kind2::Array) {
                // Witness inequality ONLY at an explicit read index where the
                // two applies differ (no default-distinctness shortcut). The
                // union of override indices is the set of indices the formula
                // can observe; extensionality witnesses appear here.
                auto applyAt = [](const ArrVal& v, const std::string& idx) {
                    auto it = v.overrides.find(idx);
                    return it != v.overrides.end() ? it->second : v.deflt;
                };
                bool anyReadDiffers = false;
                for (const auto& [idx, val] : a.arr.overrides) {
                    if (applyAt(a.arr, idx) != applyAt(b.arr, idx)) anyReadDiffers = true;
                }
                for (const auto& [idx, val] : b.arr.overrides) {
                    if (applyAt(a.arr, idx) != applyAt(b.arr, idx)) anyReadDiffers = true;
                }
                if (anyReadDiffers) return bl(false);
                // No read distinguishes them. If defaults AND all observed
                // applies agree, they are equal over everything the formula
                // can see → equal. If defaults differ but no read witnesses
                // it, we cannot soundly claim either way → indeterminate.
                if (a.arr.deflt == b.arr.deflt) return bl(true);
                return r;  // indeterminate (no default-distinctness shortcut)
            }
            if (a.kind == Kind2::Array || b.kind == Kind2::Array) return r;
            // Numbers (rational OR real-algebraic) compare EXACTLY via RealValue.
            if (a.kind == Kind2::Number && b.kind == Kind2::Number) return bl(a.n == b.n);
            // Otherwise canonical tokens (Bool/Token).
            auto at = asToken(a), bt = asToken(b);
            if (!at || !bt) return r;
            return bl(*at == *bt);
        }
        case Kind::Distinct: {
            std::vector<TR> vals;
            vals.reserve(n.children.size());
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind == Kind2::Indeterminate) return r;
                vals.push_back(cr);
            }
            bool anyIndet = false;
            for (size_t i = 0; i < vals.size(); ++i)
                for (size_t j = i + 1; j < vals.size(); ++j) {
                    // Array distinctness: only collapse to false if provably
                    // equal (defaults+reads agree); otherwise indeterminate
                    // unless a read witnesses a difference.
                    if (vals[i].kind == Kind2::Array && vals[j].kind == Kind2::Array) {
                        auto applyAt = [](const ArrVal& v, const std::string& idx) {
                            auto it = v.overrides.find(idx);
                            return it != v.overrides.end() ? it->second : v.deflt;
                        };
                        bool differs = false;
                        for (const auto& [idx, val] : vals[i].arr.overrides)
                            if (applyAt(vals[i].arr, idx) != applyAt(vals[j].arr, idx)) differs = true;
                        for (const auto& [idx, val] : vals[j].arr.overrides)
                            if (applyAt(vals[i].arr, idx) != applyAt(vals[j].arr, idx)) differs = true;
                        if (!differs) {
                            if (vals[i].arr.deflt == vals[j].arr.deflt) return bl(false);
                            anyIndet = true;  // cannot prove distinct
                        }
                        continue;
                    }
                    if (vals[i].kind == Kind2::Number && vals[j].kind == Kind2::Number) {
                        if (vals[i].n == vals[j].n) return bl(false);
                        continue;
                    }
                    auto ti = asToken(vals[i]), tj = asToken(vals[j]);
                    if (!ti || !tj) { anyIndet = true; continue; }
                    if (*ti == *tj) return bl(false);
                }
            return anyIndet ? r : bl(true);
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
        case Kind::ConstArray: {
            // const(v): λi.v. Default = token of v, no overrides.
            if (n.children.size() != 1) return r;
            TR vr = eval(n.children[0]);
            auto vt = asToken(vr);
            if (!vt) return r;
            TR t; t.kind = Kind2::Array; t.arr.deflt = *vt;
            return t;
        }
        case Kind::Store: {
            // store(a,i,v): override a at index-token(i) with token(v).
            if (n.children.size() != 3) return r;
            TR ar = eval(n.children[0]);
            if (ar.kind != Kind2::Array) return r;
            TR ir2 = eval(n.children[1]);
            TR vr = eval(n.children[2]);
            auto it = asToken(ir2);
            auto vt = asToken(vr);
            if (!it || !vt) return r;
            TR t = ar;  // copy underlying array value
            t.arr.overrides[*it] = *vt;
            return t;
        }
        case Kind::Select: {
            // select(a,i): apply a's interpretation at index-token(i).
            if (n.children.size() != 2) return r;
            TR ar = eval(n.children[0]);
            if (ar.kind != Kind2::Array) return r;
            TR ir2 = eval(n.children[1]);
            auto it = asToken(ir2);
            if (!it) return r;
            auto ov = ar.arr.overrides.find(*it);
            std::string elem = (ov != ar.arr.overrides.end()) ? ov->second : ar.arr.deflt;
            // Result is an opaque element token.
            TR t; t.kind = Kind2::Token; t.tok = elem;
            return t;
        }
        case Kind::UFApply: {
            // Evaluate an uninterpreted-function application by table lookup
            // against a supplied interpretation. Without an interpretation the
            // application is Indeterminate (the default below). The interp's
            // entries key on numeric argument tuples encoded as mpq get_str()
            // (the format CandidateModelSearch emits), so only numeric-argument
            // applications are evaluable; a non-numeric argument leaves the
            // application Indeterminate.
            if (!funcInterps_) return r;
            if (!std::holds_alternative<std::string>(n.payload.value)) return r;
            auto fit = funcInterps_->find(std::get<std::string>(n.payload.value));
            if (fit == funcInterps_->end()) return r;
            const auto& fi = fit->second;
            std::vector<std::string> argKeys;
            argKeys.reserve(n.children.size());
            for (ExprId c : n.children) {
                TR cr = eval(c);
                if (cr.kind != Kind2::Number) return r;
                // The interp keys on rational arg-strings (CMS get_str()); an
                // algebraic arg cannot match a tabulated entry.
                auto q = cr.n.tryAsRational();
                if (!q) return r;
                argKeys.push_back(q->get_str());
            }
            const std::string* valStr = &fi.deflt;
            for (const auto& e : fi.entries) {
                if (e.args == argKeys) { valStr = &e.value; break; }
            }
            if (valStr->empty()) return r;
            if (fi.retSort == "Bool") return bl(*valStr == "true" || *valStr == "1");
            try { return num(RealValue::fromMpq(mpq_class(*valStr))); } catch (...) {}
            // Non-numeric (uninterpreted-sort) result: an opaque equality token.
            TR t; t.kind = Kind2::Token; t.tok = *valStr; return t;
        }
        default:
            return r;  // quantifiers, BV/FP, … → indeterminate
    }
}

} // namespace zolver
