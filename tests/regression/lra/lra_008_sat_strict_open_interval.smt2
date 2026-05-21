; Open interval (0, 1): strict inequalities both sides — Simplex needs to find any rational inside.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (> x 0))
(assert (< x 1))
(check-sat)
