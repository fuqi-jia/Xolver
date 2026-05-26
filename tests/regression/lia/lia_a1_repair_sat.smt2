(set-logic QF_LIA)
(set-info :status sat)
; x=y with 3<=x+y<=7 has LP vertex x=y=1.5 (fractional, not reducible by
; single-variable GCD tightening), so the model survives to the Full-effort
; check. Round-to-nearest gives the feasible integer point x=y=2, which
; exercises ZOLVER_LIA_REPAIR; with the flag off branch-and-bound solves it.
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) 0))
(assert (>= (- x y) 0))
(assert (>= (+ x y) 3))
(assert (<= (+ x y) 7))
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
