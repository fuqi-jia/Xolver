(set-logic QF_UFLIA)
(set-info :status sat)
; Regression: a UF application whose argument is a boolean COMPARISON (a<=b).
; The EUF term manager cannot intern f(<=) directly; BoolSubtermPurifier must
; lift the comparison to a fresh Bool var (p <-> (a<=b)) so EUF sees f(p).
; Before that fix EufSolver set pendingUnknown_ and returned Unknown on this SAT.
(declare-fun f (Bool) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (f (<= x y)) 1))
(assert (= (f (<= y x)) 2))
(assert (< x y))
(check-sat)
