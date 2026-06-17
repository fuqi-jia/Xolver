(set-logic QF_AUFLIA)
(set-info :status unsat)
; #66 soundness regression (Bool-result variant): h:(Array Int Int)->Bool. a=b
; forces h(a)=h(b) by congruence, contradicting (not (= (h a) (h b))). The Bool
; result has no arith bridge to fall back on, so this slipped past the array
; model-validation floor as a false `sat` before the routing fix.
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun h ((Array Int Int)) Bool)
(assert (= a b))
(assert (not (= (h a) (h b))))
(check-sat)
