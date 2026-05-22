; Single variable SOS strict: x² < 0 is unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< (* x x) 0))
(check-sat)
