; #77 regression (fuzzer-derived): a third application f(0) and f((-1-2)+j) whose
; arguments are pinned equal once the linear identity forces j = 1. The chained
; ordering f(0) < f((-1-2)+j) plus the derived argument equality is unsatisfiable
; by function congruence. Previously a false sat.
(set-logic QF_UFLRA)
(set-info :status unsat)
(declare-fun i () Real)
(declare-fun j () Real)
(declare-fun k () Real)
(declare-fun f (Real) Real)
(assert (< k (f 5.0)))
(assert (< (- 1.0) (f j)))
(assert (< (f 0.0) (f (+ (- 1.0 2.0) j))))
(assert (= (+ j (- (- j (- 1.0)) j)) (- 2.0 (- (- 1.0) (- 1.0)))))
(check-sat)
