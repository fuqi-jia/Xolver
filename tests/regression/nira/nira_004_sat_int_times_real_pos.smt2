; i*r > 0 with i > 0 and r > 0 — trivially sat.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (> i 0))
(assert (> r 0))
(assert (> (* (to_real i) r) 0))
(check-sat)
