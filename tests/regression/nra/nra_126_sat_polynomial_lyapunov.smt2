; Lyapunov-like: V(x,y) = x²+y², decreasing under dynamics x'=-x+y², y'=-y.
; dV/dt = 2x*(-x+y²) + 2y*(-y) = -2x² + 2xy² - 2y² ≤ 0 in unit ball.
; Test the strict decrease: -2x² + 2xy² - 2y² < 0 for (x,y) on small annulus.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= (+ (* x x) (* y y)) (/ 1 10)))
(assert (<= (+ (* x x) (* y y)) (/ 1 4)))
(assert (< (+ (- (* 2 (* x (* y y))) (* 2 (* x x))) (- (* 2 (* y y)))) 0))
(check-sat)
