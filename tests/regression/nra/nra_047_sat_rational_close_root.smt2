; Root very close to rational — root isolation precision sensitive.
; x^2 = 2.000001 has real solutions ≈ ±1.4142139...
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (> x 0))
(assert (= (* x x) (/ 2000001 1000000)))
(check-sat)
