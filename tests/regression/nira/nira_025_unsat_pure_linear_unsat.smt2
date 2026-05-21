; Pure-linear unsat under NIRA logic: tests routing to LRA path.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (> r 100))
(assert (< r 0))
(check-sat)
