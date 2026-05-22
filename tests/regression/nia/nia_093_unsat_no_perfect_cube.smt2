; x³ ∈ {0,1,8,27,64,125,...}. Asserting x³ = 30 with x ∈ [0,10] is UNSAT.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (>= x 0)) (assert (<= x 10))
(assert (= (* x (* x x)) 30))
(check-sat)
