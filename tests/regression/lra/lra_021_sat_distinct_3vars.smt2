; distinct over 3 real vars satisfiable (continuum).
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (distinct x y z))
(check-sat)
