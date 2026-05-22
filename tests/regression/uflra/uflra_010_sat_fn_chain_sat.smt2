; f(a) < f(b) < f(c) — satisfiable.
(set-logic QF_UFLRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-const a Real) (declare-const b Real) (declare-const c Real)
(assert (< (f a) (f b)))
(assert (< (f b) (f c)))
(check-sat)
