(set-logic QF_AUFLIA)
(set-info :status unsat)
; #65/#66 regression: the minimal ios-cluster reducer. a=b => h(a)=h(b) by UF
; congruence, contradicting (distinct (h a) (h b)). Was `unknown` (the array
; model-validator floored the bogus model) before the non-arith-equality routing
; fix made (= a b) reach the shared egraph; now soundly `unsat`.
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun h ((Array Int Int)) Int)
(assert (= a b))
(assert (not (= (h a) (h b))))
(check-sat)
