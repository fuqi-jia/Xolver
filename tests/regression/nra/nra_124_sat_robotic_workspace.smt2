; Robot arm: 2-link planar arm, link lengths 1, joint angles via cos/sin polynomials.
; (cx, cy) = (cos θ1 + cos θ2, sin θ1 + sin θ2). With c=cos, s=sin.
; Each (c, s) satisfies c²+s²=1. Want endpoint within unit circle around (1,1).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const c1 Real) (declare-const s1 Real)
(declare-const c2 Real) (declare-const s2 Real)
(assert (= (+ (* c1 c1) (* s1 s1)) 1))
(assert (= (+ (* c2 c2) (* s2 s2)) 1))
(assert (<= (+ (* (- (+ c1 c2) 1) (- (+ c1 c2) 1)) (* (- (+ s1 s2) 1) (- (+ s1 s2) 1))) 1))
(check-sat)
