; Basic IDL: x - y ≤ 5, y - z ≤ 3. Transitively x - z ≤ 8.
(set-logic QF_IDL)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (<= (- x y) 5))
(assert (<= (- y z) 3))
(check-sat)
