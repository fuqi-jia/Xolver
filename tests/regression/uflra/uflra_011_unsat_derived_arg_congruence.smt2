; #77 regression: UF-over-arith congruence with a DERIVED-equal argument.
; j+1 = 2 forces j = 1, so (-1)+j = 0 and the two applications f(0), f((-1)+j)
; have value-equal arguments -> congruence forces f(0) = f((-1)+j), contradicting
; the strict f(0) < f((-1)+j). The argument equality is not syntactic (it is
; derived from the linear pin j=1), so the arrangement split must fire and the
; resulting interface disequality 0 != ((-1)+j) must be refuted by the LRA
; tableau pin. Previously a false sat.
(set-logic QF_UFLRA)
(set-info :status unsat)
(declare-fun j () Real)
(declare-fun f (Real) Real)
(assert (= (+ j 1.0) 2.0))
(assert (< (f 0.0) (f (+ (- 1.0 2.0) j))))
(check-sat)
