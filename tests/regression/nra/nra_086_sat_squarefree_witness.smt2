; Squarefree part needed: (x²-1)² = 0 — roots ±1 with multiplicity 2.
; Squarefree gives (x²-1), roots ±1. Pick x=1 with strict >0.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- (* x x) 1) (- (* x x) 1)) 0))
(assert (> x 0))
(check-sat)
