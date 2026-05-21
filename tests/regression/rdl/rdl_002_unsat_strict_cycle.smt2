; In reals, strict cycle still unsat (with negative slack).
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (- x y) 0))
(assert (< (- y x) 0))
(check-sat)
