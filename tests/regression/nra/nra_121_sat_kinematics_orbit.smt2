; Orbital kinematics: position (x,y) on circle radius r, velocity (vx,vy) tangent (vx*x + vy*y = 0),
; speed = 1. Sat with explicit (r=1, x=1, y=0, vx=0, vy=1).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const vx Real)
(declare-const vy Real)
(declare-const r Real)
(assert (> r 0))
(assert (= (+ (* x x) (* y y)) (* r r)))
(assert (= (+ (* vx x) (* vy y)) 0))
(assert (= (+ (* vx vx) (* vy vy)) 1))
(check-sat)
