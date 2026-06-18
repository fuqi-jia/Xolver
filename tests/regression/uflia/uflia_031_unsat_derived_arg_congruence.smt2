; #77 regression (integer logic): UF-over-arith congruence with a DERIVED-equal
; argument. j+1 = 2 forces j = 1, so (-1)+j = 0 and f(0), f((-1)+j) have
; value-equal arguments -> congruence forces them equal, contradicting the strict
; f(0) < f((-1)+j). The argument equality is derived (the linear pin j=1), not
; syntactic. Previously a false sat.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun j () Int)
(declare-fun f (Int) Int)
(assert (= (+ j 1) 2))
(assert (< (f 0) (f (+ (- 1 2) j))))
(check-sat)
