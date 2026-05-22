; f(a) > f(b) > f(c) > f(a) cycle on real-arg f.
(set-logic QF_UFLRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-const a Real) (declare-const b Real) (declare-const c Real)
(assert (> (f a) (f b)))
(assert (> (f b) (f c)))
(assert (> (f c) (f a)))
(check-sat)
