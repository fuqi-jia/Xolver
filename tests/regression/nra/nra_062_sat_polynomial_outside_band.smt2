; Outside a thin band: ¬(x ∈ [0.4, 0.6]) ⇔ x < 0.4 ∨ x > 0.6 — sat.
; Stress on disjunction + strict on rational endpoints.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (or (< x (/ 4 10)) (> x (/ 6 10))))
(check-sat)
