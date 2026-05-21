; Bounded product 0 ≤ i*r ≤ 1 with i ≥ 1 and r ≥ 0 — sat (e.g. i=1, r=0.5).
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (>= i 1))
(assert (>= r 0))
(assert (<= (* (to_real i) r) 1))
(check-sat)
