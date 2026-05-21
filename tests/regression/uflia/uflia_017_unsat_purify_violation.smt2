; Purification: f(x+1) and f(2) under x=1 must equal (congruence).
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= x 1))
(assert (distinct (f (+ x 1)) (f 2)))
(check-sat)
