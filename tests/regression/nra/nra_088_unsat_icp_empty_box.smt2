; ICP should detect empty box: x*y ≥ 100 with x ∈ [0,1], y ∈ [0,1].
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0)) (assert (<= x 1))
(assert (>= y 0)) (assert (<= y 1))
(assert (>= (* x y) 100))
(check-sat)
