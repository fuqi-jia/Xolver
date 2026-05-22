; Real-valued schedule with rational durations.
(set-logic QF_RDL)
(set-info :status sat)
(declare-const t1 Real) (declare-const t2 Real) (declare-const t3 Real)
(assert (>= (- t2 t1) (/ 3 2)))
(assert (>= (- t3 t2) (/ 5 2)))
(assert (>= t1 0))
(assert (<= t3 10))
(check-sat)
