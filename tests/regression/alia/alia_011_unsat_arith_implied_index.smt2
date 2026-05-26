; (+ i 1)=(+ j 1) implies i=j, so select(store(a,i,v),j)=v. Guards LIA implied-eq
; propagation to EUF.
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-const a (Array Int Int))
(declare-const i Int)(declare-const j Int)(declare-const v Int)
(assert (= (+ i 1) (+ j 1)))
(assert (not (= (select (store a i v) j) v)))
(check-sat)
