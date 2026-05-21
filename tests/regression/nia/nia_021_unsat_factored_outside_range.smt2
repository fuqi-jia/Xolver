; (x-2)(x-3) = 0 forces x∈{2,3}; x > 10 makes the system unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* (- x 2) (- x 3)) 0))
(assert (> x 10))
(check-sat)
