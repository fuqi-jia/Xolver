#include "applications/smt/qffp/Engine.h"
#include "ir/NativeBuilder.h"
#include "quantifiers/FiniteFormula.h"
#include <map>
#include <sstream>

namespace xolver::applications::smt::fp {
namespace {
using namespace xolver::native;
class Lowering {
    Nodes b;
    std::map<Node,Node> memo, variables;
    std::set<std::string> names;
    struct Format { std::size_t e,s; std::size_t width() const {return e+s;} };
    Format format(Sort sort) {
        if (!sort || !sort->isFp()) throw Unsupported("expected floating-point sort");
        Format f{sort->getExponentWidth(),sort->getSignificandWidth()};
        if (f.e<2 || f.s<2 || f.e>SIZE_MAX-f.s) throw Unsupported("invalid floating-point format");
        b.budget.tick(f.width()); return f;
    }
    Node exponent(Node x,Format f) { return b.extract(x,f.width()-2,f.s-1); }
    Node fraction(Node x,Format f) { return b.extract(x,f.s-2,0); }
    Node sign(Node x,Format f) { return b.equal(b.extract(x,f.width()-1,f.width()-1),b.bv(1,1)); }
    Node expZero(Node x,Format f) { return b.equal(exponent(x,f),b.bv(0,f.e)); }
    Node expOnes(Node x,Format f) { return b.equal(exponent(x,f),b.bv(-1,f.e)); }
    Node fracZero(Node x,Format f) { return b.equal(fraction(x,f),b.bv(0,f.s-1)); }
    Node nan(Node x,Format f) { return b.all({expOnes(x,f),b.negate(fracZero(x,f))}); }
    Node zero(Node x,Format f) { return b.all({expZero(x,f),fracZero(x,f)}); }
    Node canonical(Node x,Format f) {
        // One SMT value for every IEEE NaN encoding. Signed zeros stay distinct.
        mpz_class value=(mpz_class(1)<<f.e)-1; value<<=f.s-1; value+=1;
        return b.choose(nan(x,f),b.bv(value,f.width()),x);
    }
    static mpz_class bits(std::string text,std::size_t width) {
        int base=0;
        if (text.starts_with("#b")) base=2;
        if (text.starts_with("#x")) base=16;
        if (!base) throw Unsupported("floating-point literal must use bit fields");
        mpz_class v;
        if (mpz_set_str(v.get_mpz_t(),text.substr(2).c_str(),base) || v<0 ||
            (v!=0 && mpz_sizeinbase(v.get_mpz_t(),2)>width)) throw Unsupported("invalid floating-point bit field");
        return v;
    }
    Node literal(Node n,Format f) {
        std::istringstream in(n->getName());
        std::string tag,a,c,d,close,extra; in>>tag;
        mpz_class value=0;
        if (tag=="(fp") {
            if (!(in>>a>>c>>d)) throw Unsupported("invalid floating-point literal");
            if (!d.empty() && d.back()==')') d.pop_back();
            else if (!(in>>close) || close!=")") throw Unsupported("invalid floating-point literal terminator");
            if (in>>extra) throw Unsupported("invalid floating-point literal suffix");
            value=(bits(a,1)<<(f.width()-1))+(bits(c,f.e)<<(f.s-1))+bits(d,f.s-1);
        } else if (tag=="(_") {
            std::size_t e=0,s=0;
            if (!(in>>a>>e>>s>>close) || e!=f.e || s!=f.s || close!=")" || (in>>extra))
                throw Unsupported("invalid special floating-point literal");
            if (a=="NaN" || a=="+oo" || a=="-oo") value=((mpz_class(1)<<f.e)-1)<<(f.s-1);
            else if (a!="+zero" && a!="-zero") throw Unsupported("unknown floating-point literal");
            if (a=="NaN") value+=1;
            if (a=="-oo" || a=="-zero") mpz_setbit(value.get_mpz_t(),f.width()-1);
        } else throw Unsupported("unrecognized floating-point literal");
        return canonical(b.bv(value,f.width()),f);
    }
    Node lower(Node n) {
        Nodes::Frame frame(b);
        b.budget.tick();
        if (!n || !n->getSort()) throw Unsupported("null floating-point input");
        if (auto it=memo.find(n);it!=memo.end()) return it->second;
        const auto k=n->getKind(); const auto count=n->getChildrenSize(); const auto sort=n->getSort();
        const auto arity=[&](std::size_t ar){if(count!=ar) throw Unsupported("floating-point operator arity mismatch");};
        Node out;
        if (k==K::NT_VAR) {
            if (!names.insert(n->getName()).second) throw Unsupported("ambiguous free symbol identity");
            if (!(sort->isBool() || sort->isBv() || sort->isFp())) throw Unsupported("floating-point combination sort unavailable");
            auto raw=b.fresh(sort->isFp()?b.bvSort(format(sort).width()):sort);
            variables[n]=raw; out=sort->isFp()?canonical(raw,format(sort)):raw;
        } else if (k==K::NT_CONST && sort->isFp()) out=literal(n,format(sort));
        else if (k==K::NT_LET || k==K::NT_LET_CHAIN || k==K::NT_LET_BIND_VAR) {
            if (!count) throw Unsupported("empty let"); out=lower(n->getChild(k==K::NT_LET_CHAIN?count-1:0));
        } else if (k==K::NT_FP_TO_FP && count==3) {
            auto f=format(sort); auto x=lower(n->getChild(2));
            if (!x->getSort()->isBv() || x->getSort()->getBitWidth()!=f.width()) throw Unsupported("FP bit reinterpretation width mismatch");
            out=canonical(x,f);
        } else if (k==K::NT_FP_ABS || k==K::NT_FP_NEG) {
            arity(1); auto f=format(sort); auto x=lower(n->getChild(0));
            mpz_class mask=mpz_class(1)<<(f.width()-1);
            out=canonical(b.make(x->getSort(),k==K::NT_FP_NEG?K::NT_BV_XOR:K::NT_BV_AND,{x,b.bv(k==K::NT_FP_NEG?mask:mpz_class(mask-1),f.width())}),f);
        } else if (k==K::NT_FP_EQ || k==K::NT_FP_LT || k==K::NT_FP_LE || k==K::NT_FP_GT || k==K::NT_FP_GE) {
            arity(2); auto f=format(n->getChild(0)->getSort());
            if (!(*n->getChild(0)->getSort()==*n->getChild(1)->getSort())) throw Unsupported("FP comparison sort mismatch");
            auto x=lower(n->getChild(0)), y=lower(n->getChild(1));
            if (k==K::NT_FP_GT || k==K::NT_FP_GE) std::swap(x,y);
            auto equal=b.any({b.equal(x,y),b.all({zero(x,f),zero(y,f)})});
            auto sx=sign(x,f),sy=sign(y,f);
            auto less=b.choose(b.equal(sx,sy),b.choose(sx,b.logical(K::NT_BV_UGT,{x,y}),b.logical(K::NT_BV_ULT,{x,y})),sx);
            less=b.all({less,b.negate(equal)});
            out=b.all({b.negate(nan(x,f)),b.negate(nan(y,f)),k==K::NT_FP_EQ?equal:
                (k==K::NT_FP_LE || k==K::NT_FP_GE)?b.any({less,equal}):less});
        } else if (k>=K::NT_FP_IS_NORMAL && k<=K::NT_FP_IS_POS) {
            arity(1); auto f=format(n->getChild(0)->getSort()); auto x=lower(n->getChild(0));
            if (k==K::NT_FP_IS_NAN) out=nan(x,f);
            else if (k==K::NT_FP_IS_ZERO) out=zero(x,f);
            else if (k==K::NT_FP_IS_INF) out=b.all({expOnes(x,f),fracZero(x,f)});
            else if (k==K::NT_FP_IS_NORMAL) out=b.all({b.negate(expZero(x,f)),b.negate(expOnes(x,f))});
            else if (k==K::NT_FP_IS_SUBNORMAL) out=b.all({expZero(x,f),b.negate(fracZero(x,f))});
            else out=b.all({b.negate(nan(x,f)),k==K::NT_FP_IS_NEG?sign(x,f):b.negate(sign(x,f))});
        } else {
            if (k==K::NT_FORALL || k==K::NT_EXISTS || k==K::NT_UF_APPLY || k==K::NT_FUNC_APPLY ||
                k==K::NT_QUANT_VAR || (k>=K::NT_FP_ADD && k<=K::NT_FP_IS_POS))
                throw Unsupported("floating-point operator requires an additional backend");
            if (!(sort->isBool() || sort->isBv() || sort->isFp() || ((sort->isInt() || sort->isIntOrReal()) && k==K::NT_CONST)))
                throw Unsupported("floating-point mixed theory signature unavailable");
            std::vector<Node> args; for (auto c:SOMTParser::children(n)) args.push_back(lower(c));
            out=b.make(sort->isFp()?b.bvSort(format(sort).width()):sort,k,args,n->getName());
        }
        memo[n]=out; return out;
    }
public:
    Lowering(const NativeAssertions& roots,std::size_t work):b(roots,work) {}
    SolverAnswer solve(const NativeAssertions& roots,quantifiers::Limits limits) {
        NativeAssertions encoded; for(auto root:roots) encoded.push_back(lower(root));
        auto answer=quantifiers::bitvector::solve(encoded,limits);
        if (answer.result!=Result::Sat || !answer.model) return answer;
        auto raw=*answer.model; answer.model.emplace();
        for (const auto& [input,term]:variables) {
            auto text=quantifiers::finiteValue(term,raw); if(!text) throw Unsupported("FP model reconstruction failed");
            if (!input->getSort()->isFp()) answer.model->assignments[input->getName()]=*text;
            else {
                auto f=format(input->getSort());
                auto s=quantifiers::finiteValue(b.extract(term,f.width()-1,f.width()-1),raw);
                auto e=quantifiers::finiteValue(exponent(term,f),raw),m=quantifiers::finiteValue(fraction(term,f),raw);
                if(!s || !e || !m) throw Unsupported("FP field model reconstruction failed");
                answer.model->assignments[input->getName()]="#smt:(fp "+*s+" "+*e+" "+*m+")";
            }
        }
        return answer;
    }
};
}
SolverAnswer solve(const NativeAssertions& roots,quantifiers::Limits limits) {
    try { return Lowering(roots,limits.work).solve(roots,limits); }
    catch(const Unsupported& e) {SolverAnswer a;a.reason=e.what();return a;}
    catch(const ResourceExhausted& e) {SolverAnswer a;a.reason=e.what();return a;}
    catch(const std::bad_alloc&) {SolverAnswer a;a.reason="floating-point memory exhausted";return a;}
}
}
