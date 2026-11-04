; The same congruence obligation holds for real-valued UF arguments.
(set-logic QF_UFLRA)
(set-info :status unsat)
(declare-const x Real)
(declare-fun f (Real) Real)
(assert (not (or (not (and (= x 4) (= (f x) 7) (distinct (f 4) 7))) false)))
(check-sat)
