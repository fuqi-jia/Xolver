; Negative cycle: x - y ≤ -1, y - x ≤ -1. Bellman-Ford must detect.
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) (- 1)))
(assert (<= (- y x) (- 1)))
(check-sat)
