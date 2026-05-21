; SAT control: simple non-cyclic RDL chain.
(set-logic QF_RDL)
(set-info :status sat)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (- a b) 1))
(assert (<= (- b c) 1))
(check-sat)
