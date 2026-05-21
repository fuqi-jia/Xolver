; 4x + 6y = 5 has no integer solution (gcd(4,6)=2 does not divide 5).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 4 x) (* 6 y)) 5))
(check-sat)
