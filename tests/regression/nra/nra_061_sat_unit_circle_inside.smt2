; Sub-unit ball + strict: x² + y² < 1 with witness (0,0).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ (* x x) (* y y)) 1))
(check-sat)
