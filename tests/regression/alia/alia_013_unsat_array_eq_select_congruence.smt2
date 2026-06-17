(set-logic QF_ALIA)
(set-info :status unsat)
; #66 soundness regression (pure array+LIA, no UF): a=b between two array
; variables. select congruence gives select(a,i)=select(b,i), contradicting
; (select a i)=0 ^ (select b i)=1. (= a b) over array operands must route to EUF
; (the array reasoner), not to arith as an opaque a-b=0 polynomial.
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (= a b))
(assert (= (select a i) 0))
(assert (= (select b i) 1))
(check-sat)
