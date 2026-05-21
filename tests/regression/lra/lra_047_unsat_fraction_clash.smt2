; Fraction equality conflict.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= x (/ 1 3)))
(assert (= x (/ 1 4)))
(check-sat)
