; Disjoint bound intervals.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (>= x 10))
(assert (<= x (- 10)))
(check-sat)
