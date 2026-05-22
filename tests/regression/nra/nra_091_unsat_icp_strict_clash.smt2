; x*y < 0 with both x>0 and y>0 — ICP must reject quickly.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (> x 0)) (assert (> y 0))
(assert (< (* x y) 0))
(check-sat)
