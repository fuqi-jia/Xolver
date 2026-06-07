(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

KochanskiPiApproximation:
 Kochański's Pi Approximation:Let M, B be arbitrary points. Let A be the regular 4-gon with vertices B, M, A, C_1. Let C be the a mirrored at M. Let poly2 be the regular 3-gon with vertices M, B, Y. Let r be the segment M, B. Let n be the line through C parallel to r. Let p be the ray through M, Y. Let X be the intersection of n and p. Let u be the vector(B, M). Let D be the x + u. Let E be the d + u. Let Z be the e + u. Let q be the segment A, Z. Compare segment A, Z and segment M, B.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v14 () Real)
(declare-fun v23 () Real)
(declare-fun v28 () Real)
(declare-fun v29 () Real)
(assert (and (< 0 m) (< 0 v28) (< 0 v29) (= (+ (* v23 v23) (* (* v28 v28) (- 1) )(* v23 (- 2) )5) 0) (= (+ (* (* v14 v14) 4) (- 3) )0) (= (+ (* (* v14 v23) (- 2) )(* v14 (- 4) )1) 0) (= (+ (* m (- 1) )v28) 0) (= (+ (* v29 (- 1) )1) 0)))
(check-sat)
(exit)
