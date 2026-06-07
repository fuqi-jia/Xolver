(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Median_Perimeter_a2:
 Comparison of Medians and Perimeter via realgeom (Isosceles Triangle, ver. a2) :Let B_2, B_1 be arbitrary points. Let a be the segment B_2, B_1. Let g be the perpendicular bisector of a. Let A be a point on g. Let b be the segment B_2, A. Let D be the midpoint of B_2, B_1. Let E be the midpoint of B_2, A. Let m_a be the segment A, D. Let m_b be the segment E, B_1. Compare a + 2b and m_a + 2m_b.

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
(assert (and (< 0 m) (< 0 v17) (< 0 v18) (< 0 v15) (< 0 v16) (= (+ (* (* v14 v14) 16) (* (* v17 v17) (- 16) )9) 0) (= (- (* (* v14 v14) 4) (* v18 v18)) 0) (= (+ (* (* v14 v14) 16) (* (* v15 v15) (- 4) )1) 0) (= (+ (* v16 (- 1) )1) 0) (= (+ (* (* m v17) (- 2) )(* (* m v18) (- 1) )(* v15 2) 1) 0)))
(check-sat)
(exit)
