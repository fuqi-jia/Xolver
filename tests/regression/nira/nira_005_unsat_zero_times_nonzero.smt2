; 0 * r > 0 is impossible regardless of r.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const i Int)
(declare-const r Real)
(assert (= i 0))
(assert (> (* (to_real i) r) 0))
(check-sat)
