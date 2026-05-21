; Implication: (and (>= x 5) (<= x 5)) ⇒ x = 5; then assert x != 5.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (and (>= x 5) (<= x 5)))
(assert (distinct x 5))
(check-sat)
