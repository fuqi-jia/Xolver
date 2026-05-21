; Strict differences forming a cycle (with integers, < becomes ≤ -1).
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (< (- x y) 0))
(assert (< (- y x) 0))
(check-sat)
