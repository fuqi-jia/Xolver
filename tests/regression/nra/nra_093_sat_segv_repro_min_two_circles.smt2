; SEGV minimization from nra_065. Strip the `y=x` line — keep two intersecting circles.
; If this still SEGVs, the bug is in bivariate algebraic isolation, not sector lifting under linear substitution.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= (+ (* (- x 1) (- x 1)) (* y y)) 1))
(check-sat)
