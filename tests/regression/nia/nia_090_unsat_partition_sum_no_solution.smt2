; Sum of 3 distinct positive squares ≥ 1+4+9=14. Asserting sum = 13 ⇒ UNSAT.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int) (declare-const y Int) (declare-const z Int)
(assert (>= x 1)) (assert (>= y 1)) (assert (>= z 1))
(assert (distinct x y z))
(assert (= (+ (* x x) (* y y) (* z z)) 13))
(check-sat)
