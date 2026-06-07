(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoRightTriangle-Bottema8.1b:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 8.1 (isosceles right triangle, ver. b):Let B, A be arbitrary points. Let c be the segment A, B. Let M be the midpoint of c. Let f be the line through M perpendicular to c. Let d be the circle through B with center M. Let C be the intersection point of d, f. Let M_B be the midpoint of A, C. Let m_b be the segment M_B, B. Let m_c be the segment M, C. Let a be the segment C, B. Let b be the segment A, C. Compare m_c + 2m_b and a + b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v16) (< 0 v14) (< 0 v13) (< 0 v15) (= (+ (* (* v12 v12) (- 16) )1) 0) (= (- (* (* v12 v12) 4) (* v14 v14)) 0) (= (+ (* (* v12 v12) 16) (* (* v17 v17) (- 4) )1) 0) (= (+ (* (* v12 v12) 16) (* (* v13 v13) (- 16) )9) 0) (= (+ (* (* v12 v12) 16) (* (* v16 v16) (- 4) )1) 0) (= (+ (* v15 (- 1) )1) 0) (= (+ (* (* m v16) (- 1) )(* (* m v17) (- 1) )(* m (- 1) )(* v13 2) v14) 0)))
(check-sat)
(exit)
