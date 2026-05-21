; x^2 = -1 has no real solution.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* x x) (- 1)))
(check-sat)
