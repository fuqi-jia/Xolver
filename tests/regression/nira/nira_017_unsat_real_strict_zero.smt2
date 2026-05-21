; r*r > 0 ∧ r = 0 is unsat.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (> (* r r) 0))
(assert (= r 0))
(check-sat)
