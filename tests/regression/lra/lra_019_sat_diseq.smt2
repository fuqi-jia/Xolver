; Disequality on reals — always satisfiable as long as not pinned to equal.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0))
(assert (>= y 0))
(assert (distinct x y))
(check-sat)
