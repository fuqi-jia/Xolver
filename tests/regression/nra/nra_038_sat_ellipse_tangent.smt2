; Ellipse x²/4 + y² = 1 tangent to y = 1 at (0, 1). Single solution.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (/ (* x x) 4) (* y y)) 1))
(assert (= y 1))
(check-sat)
