; x^4 + x^2 + 1 = 0 has no real root (always > 0). Stresses high-degree
; resolvent / Sturm sequence in CDCAC projection.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (+ (* (* x x) (* x x)) (* x x) 1) 0))
(check-sat)
