; x = y combined with x != y is unsat.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= x y))
(assert (distinct x y))
(check-sat)
