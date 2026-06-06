(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema6.1a:
 Comparison of Sum of Heights and Perimeter via realgeom, Bottema 6.1 (right triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let M be the midpoint of c. Let d be the circle through B with center M. Let C be a point on d. Let b be the segment A, C. Let a be the segment C, B. Let f be the line through C perpendicular to c. Let D be the intersection of f and c. Let h_c be the segment C, D. Compare a + b + h_c and a + b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(assert (and (< 0 m) (< 0 v15) (< 0 v14) (< 0 v13) (< 0 v16) (= (+ (* (* v10 v10) (- 1) )(* (* v11 v11) (- 1) )(* v10 2) v11 (- 1) )0) (= (+ (* v10 v10) (* v11 v11) (* (* v14 v14) (- 1) )(* v10 (- 2) )(* v11 (- 2) )2) 0) (= (+ (* v10 v10) (* (* v15 v15) (- 1) )(* v10 (- 2) )1) 0) (= (+ (* v10 v10) (* v11 v11) (* (* v13 v13) (- 1) )(* v10 (- 2) )1) 0) (= (+ (* v16 (- 1) )1) 0) (= (+ (* (* m v13) (- 1) )(* (* m v14) (- 1) )(* m (- 1) )v13 v14 v15) 0)))
(check-sat)
(exit)
