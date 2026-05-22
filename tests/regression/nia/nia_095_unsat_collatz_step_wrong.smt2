; Collatz: n=5 (odd) ⇒ n_next = 16. Assert n_next = 8 ⇒ UNSAT.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const n Int)
(declare-const n_next Int)
(assert (= n 5))
(assert (= n_next (ite (= (mod n 2) 0) (div n 2) (+ (* 3 n) 1))))
(assert (= n_next 8))
(check-sat)
