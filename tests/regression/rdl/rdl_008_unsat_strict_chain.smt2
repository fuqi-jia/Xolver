; 4-node strict difference cycle.
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const a Real) (declare-const b Real) (declare-const c Real) (declare-const d Real)
(assert (< (- a b) 0))
(assert (< (- b c) 0))
(assert (< (- c d) 0))
(assert (< (- d a) 0))
(check-sat)
