; 2*r^2 - 3*r + 1 = 0 has roots 1 and 1/2 — sat.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(assert (= (- (* 2 (* r r)) (- (* 3 r) 1)) 0))
(check-sat)
