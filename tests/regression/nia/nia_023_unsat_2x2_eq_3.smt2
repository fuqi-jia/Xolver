; 2x^2 = 3 has no integer x (3 is not 2*square).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* 2 (* x x)) 3))
(check-sat)
