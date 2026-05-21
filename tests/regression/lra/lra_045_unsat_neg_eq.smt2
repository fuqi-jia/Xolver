; ¬(x = y) ∧ x = 0 ∧ y = 0 unsat.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (not (= x y)))
(assert (= x 0))
(assert (= y 0))
(check-sat)
