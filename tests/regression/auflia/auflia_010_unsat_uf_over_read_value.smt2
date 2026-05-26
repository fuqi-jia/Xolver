; f(select a i) with select(a,i)=5 forces f(select a i)=f(5) by congruence.
; Guards the purified-UFApply payload (function-name) preservation fix.
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-const a (Array Int Int))
(declare-fun f (Int) Int)
(declare-const i Int)
(assert (= (f (select a i)) 2))
(assert (= (select a i) 5))
(assert (not (= (f 5) 2)))
(check-sat)
