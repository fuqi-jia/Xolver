; x^2 + y^2 + 1 ≤ 0 — always positive, unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y) 1) 0))
(check-sat)
