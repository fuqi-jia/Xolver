; x^3 = 7 has no integer solution.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* x (* x x)) 7))
(check-sat)
