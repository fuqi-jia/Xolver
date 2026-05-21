; x * 0 = 1 has no solution.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* x 0) 1))
(check-sat)
