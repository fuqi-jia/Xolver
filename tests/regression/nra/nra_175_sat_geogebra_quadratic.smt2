(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema8.1a:
 Comparison of Sums of Medians and Perimeter via RealGeom, Bottema 8.1 (isosceles triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let d be the circle through B with center A. Let C be a point on d. Let a be the segment B, C. Let D be the midpoint of a. Let m_a be the segment A, D. Let E be the midpoint of c. Let m_c be the segment C, E. Compare m_a + 2m_c and a + 2c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(assert (and (< 0 m) (< 0 v12) (< 0 v11) (< 0 v13) (< 0 v14) (= (+ (* (* v12 v12) (- 4) )(* (* v7 v7) 16) (* (* v8 v8) 16) (* v7 (- 24) )9) 0) (= (+ (* (* v13 v13) (- 1) )(* (* v7 v7) 4) (* (* v8 v8) 4) (* v7 (- 8) )4) 0) (= (+ (* (* v7 v7) (- 4) )(* (* v8 v8) (- 4) )(* v7 4)) 0) (= (+ (* (* v11 v11) (- 1) )(* v7 v7) (* v8 v8)) 0) (= (+ (* v14 (- 1) )1) 0) (= (+ (* (* m v13) (- 1) )(* m (- 2) )v11 (* v12 2)) 0)))
(check-sat)
(exit)
