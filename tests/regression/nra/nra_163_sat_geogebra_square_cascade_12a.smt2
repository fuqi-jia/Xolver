; Geogebra algebraic-SAT (square-cascade). z3=sat.
(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.
IsoRightTriangle-Bottema1.12a:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 1.12 (isosceles right triangle, ver. a):Let C, A be arbitrary points. Let b be the segment C, A. Let d be the circle through A with center C. Let f be the line through C perpendicular to b. Let B be the intersection point of d, f. Let c be the segment B, A. Let a be the segment B, C. Compare (a + b + c)^3 (a + b - c) (b + c - a) (c + a - b) and a^2 b^2 c^2.
This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v11) (< 0 v10) (< 0 v9) (= (+ (* (* v8 v8) (- 1) )1) 0) (= (+ (* (* v10 v10) (- 1) )(* v8 v8) 1) 0) (= (+ (* (* v11 v11) (- 1) )(* v8 v8)) 0) (= (+ (* v9 (- 1) )1) 0) (= (+ (* (* v10 v10 v10 v10 v10 v10) (- 1) )(* (* (* v10 v10 v10 v10 v10) v11) (- 2) )(* (* v10 v10 v10 v10) (* v11 v11)) (* (* (* v10 v10 v10) (* v11 v11 v11)) 4) (* (* v10 v10) (* v11 v11 v11 v11)) (* (* v10 (* v11 v11 v11 v11 v11)) (- 2) )(* (* v11 v11 v11 v11 v11 v11) (- 1) )(* (* m (* v10 v10) (* v11 v11)) (- 1) )(* (* v10 v10 v10 v10 v10) (- 2) )(* (* (* v10 v10 v10 v10) v11) (- 2) )(* (* (* v10 v10 v10) (* v11 v11)) 4) (* (* (* v10 v10) (* v11 v11 v11)) 4) (* (* v10 (* v11 v11 v11 v11)) (- 2) )(* (* v11 v11 v11 v11 v11) (- 2) )(* v10 v10 v10 v10) (* (* (* v10 v10 v10) v11) 4) (* (* (* v10 v10) (* v11 v11)) 6) (* (* v10 (* v11 v11 v11)) 4) (* v11 v11 v11 v11) (* (* v10 v10 v10) 4) (* (* (* v10 v10) v11) 4) (* (* v10 (* v11 v11)) 4) (* (* v11 v11 v11) 4) (* v10 v10) (* (* v10 v11) (- 2) )(* v11 v11) (* v10 (- 2) )(* v11 (- 2) )(- 1) )0)))
(check-sat)
(exit)
