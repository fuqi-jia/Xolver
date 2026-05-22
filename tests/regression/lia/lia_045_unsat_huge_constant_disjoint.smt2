; 10^18 + 10^18 ≠ 1 — must check large arithmetic.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= x 1000000000000000000))
(assert (= (* 2 x) 1))
(check-sat)
