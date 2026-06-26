(set-logic QF_AUFLIA)
(set-info :status unsat)
; #66 soundness regression: a UF h over arrays with an array equality between two
; bare array VARIABLES. (= a b) has no array OPERATOR, so the atomizer must still
; route it to EUF (congruence), NOT to arith as an opaque a-b=0 polynomial.
; a=b => h(a)=h(b), contradicting h(a)=0 ^ h(b)=1. Was a false `sat` before the
; Nelson-Oppen non-arith-equality routing fix (Atomizer.cpp).
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun h ((Array Int Int)) Int)
(assert (= a b))
(assert (= (h a) 0))
(assert (= (h b) 1))
(check-sat)
