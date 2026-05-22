; UFLRA: distinct outputs over distinct inputs — sat.
(set-logic QF_UFLRA)
(set-info :status sat)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-const a Real) (declare-const b Real)
(assert (distinct a b))
(assert (distinct (f a) (f b)))
(check-sat)
