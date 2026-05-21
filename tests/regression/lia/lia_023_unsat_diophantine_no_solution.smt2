; gcd(6, 9) = 3 does not divide 7 ⇒ no integer solution.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 6 x) (* 9 y)) 7))
(check-sat)
