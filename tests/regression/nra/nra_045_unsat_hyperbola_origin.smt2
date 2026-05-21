; xy = 1 AND x = 0 — unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (* x y) 1))
(assert (= x 0))
(check-sat)
