; Polynomial with negative leading coefficient that should be sat.
; -x^2 + 4 > 0 ⇔ |x| < 2.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (> (- 4 (* x x)) 0))
(check-sat)
