(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

OposicionsSecundariaCatalunya2018-2.4a:
 Comparison of two segments in Exercise 2.4 of Oposicions Secundària Catalunya 2018 via realgeom (a regular triangle and two reflections, ver. a):Let A, B be arbitrary points. Let poly1 be the regular 3-gon with vertices A, B, C. Let h be the segment C, A. Let F be the midpoint of A, C. Let G be the midpoint of A, B. Let B' be the b mirrored at h. Let B'' be the b mirrored at A. Let i be the segment B'', F. Let j be the segment G, B'. Let D be the intersection of i and j. Let k be the segment D, A. Compare segment G, B' and segment D, A.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v21 () Real)
(declare-fun v22 () Real)
(declare-fun v24 () Real)
(declare-fun v25 () Real)
(declare-fun v6 () Real)
(assert (and (< 0 m) (< 0 v25) (< 0 v24) (= (- (* (* v15 v6) 2) v16) 0) (= (+ (* (* v16 v6) 2) v15 (- 1) )0) (= (+ (* (* v15 v15) 16) (* (* v16 v16) 16) (* (* v24 v24) (- 4) )(* v15 (- 24) )9) 0) (= (+ (* (* v21 v6) (- 2) )(* v22 5) (* v6 (- 2))) 0) (= (+ (* (* v15 v22) 4) (* (* v16 v21) (- 4) )(* v16 2) (* v22 (- 3))) 0) (= (+ (* (* v6 v6) 4) (- 3) )0) (= (+ (* v21 v21) (* v22 v22) (* (* v25 v25) (- 1))) 0) (= (+ (* (* m v25) (- 1) )v24) 0)))
(check-sat)
(exit)
