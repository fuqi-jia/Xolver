; Smaller circle inside bigger — tests cell containment lifting.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 4))
(assert (<= (+ (* x x) (* y y)) 1))
(check-sat)
