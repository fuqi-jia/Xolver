(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema8.1b:
 Comparison of Sum of Medians and Perimeter via realgeom, Bottema 8.1 (isosceles triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let g be the perpendicular bisector of c. Let C be a point on g. Let b be the segment A, C. Let D be the midpoint of A, B. Let E be the midpoint of A, C. Let m_c be the segment C, D. Let m_b be the segment E, B. Compare 2m_b + m_c and 2b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(assert (and (< 0 m) (< 0 v16) (< 0 v15) (< 0 v18) (< 0 v17) (= (- (* (* v14 v14) 4) (* v15 v15)) 0) (= (+ (* (* v14 v14) 16) (* (* v16 v16) (- 16) )9) 0) (= (+ (* (* v14 v14) 16) (* (* v18 v18) (- 4) )1) 0) (= (+ (* v17 (- 1) )1) 0) (= (+ (* (* m v18) (- 2) )(* m (- 1) )v15 (* v16 2)) 0)))
(check-sat)
(exit)
