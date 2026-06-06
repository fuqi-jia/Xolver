(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema8.1b:
 Comparison of Sum of Medians and Perimeter via realgeom, Bottema 8.1 (right triangle, ver. b1):Let C, B be arbitrary points. Let a be the segment C, B. Let f be the line through C perpendicular to a. Let A be a point on f. Let c be the segment A, B. Let b be the segment C, A. Let M3 be the midpoint of c. Let m_c be the segment C, M3. Let M1 be the midpoint of a. Let M2 be the midpoint of b. Let m_a be the segment A, M1. Let m_b be the segment B, M2. Compare m_a + m_b + m_c and a + b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v20 () Real)
(declare-fun v8 () Real)
(assert (and (< 0 m) (< 0 v15) (< 0 v16) (< 0 v17) (< 0 v19) (< 0 v18) (< 0 v20) (= (+ (* (* v15 v15) (- 4) )(* v8 v8) 4) 0) (= (+ (* (* v16 v16) (- 4) )(* (* v8 v8) 4) 1) 0) (= (+ (* (* v18 v18) (- 1) )(* v8 v8) 1) 0) (= (+ (* (* v19 v19) (- 1) )(* v8 v8)) 0) (= (+ (* (* v17 v17) (- 4) )(* v8 v8) 1) 0) (= (+ (* v20 (- 1) )1) 0) (= (+ (* (* m v18) (- 1) )(* (* m v19) (- 1) )(* m (- 1) )v15 v16 v17) 0)))
(check-sat)
(exit)
