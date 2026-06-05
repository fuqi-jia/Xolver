; Regression for the variable-order-induced false-UNSAT fixed by the Brown CAD
; ordering default (commit 3068210). Minimised (delta-debug) from Geogebra
; IsoRightTriangle-Bottema1.4b. The variable m is DETERMINED by the later
; variables (linear, only in the trilinear constraint); with the old alphabetical
; order m was assigned FIRST, its axis was delineated only by m>0, the covering
; sampled one sector rep (m=1) which conflicts, and the whole feasible region
; (m > ~4.12) was wrongly excluded -> false UNSAT. Brown's order assigns m LAST
; (lowest total degree projected first), pinning it by an exact root. z3 = sat.
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v13 () Real)
(assert (< 0 m))
(assert (< 0 v13))
(assert (< 0 v11))
(assert (= (+ (* (* v10 v10) (- 4) )1) 0))
(assert (= (+ (* (* v10 v10) 4) (* (* v11 v11) (- 4) )1) 0))
(assert (= (+ (* (* m v11 v13) (- 1) )(* (* v11 v11) v13) (* v11 (* v13 v13)) (* v11 v11) (* (* v11 v13) 2) (* v13 v13) v11 v13) 0))
(check-sat)
