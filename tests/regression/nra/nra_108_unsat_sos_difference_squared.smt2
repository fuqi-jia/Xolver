; (x-y)² < 0 — single squared difference.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (* (- x y) (- x y)) 0))
(check-sat)
