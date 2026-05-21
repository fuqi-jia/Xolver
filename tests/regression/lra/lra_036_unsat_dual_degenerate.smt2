; Same LHS, different RHS — dual degeneracy + conflict.
(set-logic QF_LRA)

(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ x y) 1))
(assert (= (+ x y) 2))
(check-sat)
