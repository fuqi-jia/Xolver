; x^2 + y^2 ≤ -1 — unsat (sum of squares ≥ 0). Tests NIA square-positivity rule.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* x x) (* y y)) (- 1)))
(check-sat)
