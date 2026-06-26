; Omega-test target: the nonlinear monomial (x*y) abstracts to a free integer X,
; leaving 2*X + 4*w = 1. The coefficient gcd (2) never divides 1, so no integer
; solution exists — the Omega normalize stage's gcd screen proves it. z3-confirmed.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(declare-const w Int)
(assert (= (+ (* 2 (* x y)) (* 4 w)) 1))
(check-sat)
