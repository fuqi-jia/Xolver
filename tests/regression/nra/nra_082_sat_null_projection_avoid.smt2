; Polynomial where naive projection vanishes: y*(x-1) = 0 AND y > 0 ⇒ x=1.
; Tests NullificationAnalyzer detection.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (* y (- x 1)) 0))
(assert (> y 0))
(check-sat)
