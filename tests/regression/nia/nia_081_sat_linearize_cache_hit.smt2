; Same nonlinear term `x*y` appears 3× — Linearization cache must hit twice.
; All three constraints consistent with (x=1, y=1).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1)) (assert (<= x 2))
(assert (>= y 1)) (assert (<= y 2))
(assert (>= (* x y) 1))
(assert (<= (* x y) 4))
(assert (= (* x y) (* x y)))   ; tautological refer to xy
(check-sat)
