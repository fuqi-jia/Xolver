(set-logic QF_AUFLIA)
(set-info :status unsat)
; UF over an array read; Row1 forces select(store(a,i,v),i)=v, so f values agree
(declare-fun f (Int) Int)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (not (= (f (select (store a i v) i)) (f v))))
(check-sat)
