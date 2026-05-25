(set-logic QF_ALIA)
(set-info :status unsat)
; store value coupled to arith: read of just-written cell must equal stored 7
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const x Int)
(assert (= (select (store a i 7) i) x))
(assert (not (= x 7)))
(check-sat)
