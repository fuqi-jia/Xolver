(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoRightTriangle-Bottema1.23b:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 1.23 (isosceles right triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let M be the midpoint of c. Let d be the circle through B with center M. Let f be the line through M perpendicular to c. Let C be the intersection point of d, f. Let a be the segment C, B. Let b be the segment A, C. Compare a b(a + b) + b c(b + c) + c a(c + a) and (a + b + c)^3 + 3a b c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(assert (and (< 0 m) (< 0 v12) (< 0 v11) (< 0 v13) (= (+ (* (* v10 v10) (- 4) )1) 0) (= (+ (* (* v10 v10) 4) (* (* v11 v11) (- 4) )1) 0) (= (+ (* (* v10 v10) 4) (* (* v12 v12) (- 4) )1) 0) (= (+ (* v13 (- 1) )1) 0) (= (+ (* (* m (* v11 v11 v11)) (- 1) )(* (* m (* v11 v11) v12) (- 3) )(* (* m v11 (* v12 v12)) (- 3) )(* (* m (* v12 v12 v12)) (- 1) )(* (* m (* v11 v11)) (- 3) )(* (* m v11 v12) (- 9) )(* (* m (* v12 v12)) (- 3) )(* (* v11 v11) v12) (* v11 (* v12 v12)) (* (* m v11) (- 3) )(* (* m v12) (- 3) )(* v11 v11) (* v12 v12) (* m (- 1) )v11 v12) 0)))
(check-sat)
(exit)
