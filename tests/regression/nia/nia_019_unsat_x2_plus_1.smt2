; x^2 + 1 = 0 has no integer solution.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (+ (* x x) 1) 0))
(check-sat)
