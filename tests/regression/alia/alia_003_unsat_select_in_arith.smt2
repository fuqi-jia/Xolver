(set-logic QF_ALIA)
(set-info :status unsat)
; select value used in arithmetic: (select a i)=3 and (select a i)>5 contradict
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select a i) 3))
(assert (> (select a i) 5))
(check-sat)
