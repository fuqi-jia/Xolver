; x^2 = 4 AND x^2 = 9 — disjoint solutions ⇒ unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* x x) 4))
(assert (= (* x x) 9))
(check-sat)
