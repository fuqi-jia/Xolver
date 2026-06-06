(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

Odom-GoldenRatio-RegTriangle:
 Constructing the Golden Ratio (Odom's theorem, 1983):Let X, Y be arbitrary points. Let poly1 be the regular 3-gon with vertices X, Y, Z. Let g be the segment Y, Z. Let h be the segment Z, X. Let c be the circle through X, Y, Z. Let S be the midpoint of g. Let A be the midpoint of h. Let i be the line S, A. Let B be the intersection of c and i. Let AS be the segment A, S. Let SB be the segment S, B. Compare segment A, S and segment S, B.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v15 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v8 () Real)
(assert (and (< 0 m) (< 0 v19) (< 0 v18) (= (+ (* (* v15 v15) 16) (* (* v19 v19) (- 16) )(* v15 (- 24) )9) 0) (= (+ (* (* v8 v8) 4) (- 3) )0) (= (+ (* (* v10 v8) 8) (* (* v8 v8) (- 4) )1) 0) (= (+ (* (* v10 v8) 4) (* (* v15 v15) (- 4) )(* (* v8 v8) (- 1) )(* v15 4)) 0) (= (+ (* (* m v19) (- 2) )1) 0) (= (+ (* v18 (- 2) )1) 0)))
(check-sat)
(exit)
