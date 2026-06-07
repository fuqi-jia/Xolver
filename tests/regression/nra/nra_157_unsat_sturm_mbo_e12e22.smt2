; Sturm-MBO UNSAT: xolver solves in ~450ms; z3 times out (>20s). Second of the
; xolver-beats-z3 Sturm-MBO wins from the 70-case random differential.
(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E12E22|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* (* h1 h1 h1) (* h2 h2) h5 (* j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) h5 
(* j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h5 (* j2 j2)) (* 36 (* h1 h1 h1) (* 
h2 h2) h5 j2) (* 16 (* h1 h1 h1) (* h2 h2) h5) (* (* h1 h1 h1) (* h2 h2) h6 (* 
j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2 j2)) (* 28 (* h1 h1 h1) 
(* h2 h2) h6 (* j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2) h6 j2) (* 16 (* h1 h1 h1) 
(* h2 h2) h6) (* 3 (* h1 h1 h1) h2 h3 h4 (* j2 j2 j2 j2)) (* 23 (* h1 h1 h1) h2 
h3 h4 (* j2 j2 j2)) (* 56 (* h1 h1 h1) h2 h3 h4 (* j2 j2)) (* 52 (* h1 h1 h1) h2
 h3 h4 j2) (* 16 (* h1 h1 h1) h2 h3 h4) (* 12 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2 
j2)) (* 92 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2)) (* 224 (* h1 h1 h1) h2 h3 h5 (* 
j2 j2)) (* 208 (* h1 h1 h1) h2 h3 h5 j2) (* 64 (* h1 h1 h1) h2 h3 h5) (* 12 (* 
h1 h1 h1) h2 h3 h6 (* j2 j2 j2 j2)) (* 92 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2)) 
(* 224 (* h1 h1 h1) h2 h3 h6 (* j2 j2)) (* 208 (* h1 h1 h1) h2 h3 h6 j2) (* 64 
(* h1 h1 h1) h2 h3 h6) (* 4 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2 j2)) (* 32 (* h1 
h1 h1) h2 h4 h5 (* j2 j2 j2)) (* 84 (* h1 h1 h1) h2 h4 h5 (* j2 j2)) (* 88 (* h1
 h1 h1) h2 h4 h5 j2) (* 32 (* h1 h1 h1) h2 h4 h5) (* 2 (* h1 h1 h1) h2 h4 h6 (* 
j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 h4 h6 (* j2 j2 j2)) (* 42 (* h1 h1 h1) h2 h4
 h6 (* j2 j2)) (* 44 (* h1 h1 h1) h2 h4 h6 j2) (* 16 (* h1 h1 h1) h2 h4 h6) (* 
(* h1 h1 h1) h2 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) h2 (* h5 h5) 
(* j2 j2 j2 j2)) (* 53 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2 j2)) (* 106 (* h1 h1 
h1) h2 (* h5 h5) (* j2 j2)) (* 96 (* h1 h1 h1) h2 (* h5 h5) j2) (* 32 (* h1 h1 
h1) h2 (* h5 h5)) (* 2 (* h1 h1 h1) h2 h5 h6 (* j2 j2 j2 j2 j2)) (* 24 (* h1 h1 
h1) h2 h5 h6 (* j2 j2 j2 j2)) (* 106 (* h1 h1 h1) h2 h5 h6 (* j2 j2 j2)) (* 212 
(* h1 h1 h1) h2 h5 h6 (* j2 j2)) (* 192 (* h1 h1 h1) h2 h5 h6 j2) (* 64 (* h1 h1
 h1) h2 h5 h6) (* (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1 
h1) h2 (* h6 h6) (* j2 j2 j2 j2)) (* 53 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2)) 
(* 106 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2)) (* 96 (* h1 h1 h1) h2 (* h6 h6) j2) 
(* 32 (* h1 h1 h1) h2 (* h6 h6)) (* 18 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2 j2)
) (* 114 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2)) (* 200 (* h1 h1 h1) (* h3 h3) 
h4 (* j2 j2)) (* 136 (* h1 h1 h1) (* h3 h3) h4 j2) (* 32 (* h1 h1 h1) (* h3 h3) 
h4) (* 36 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 228 (* h1 h1 h1) (* h3 
h3) h5 (* j2 j2 j2)) (* 400 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2)) (* 272 (* h1 h1
 h1) (* h3 h3) h5 j2) (* 64 (* h1 h1 h1) (* h3 h3) h5) (* 36 (* h1 h1 h1) (* h3 
h3) h6 (* j2 j2 j2 j2)) (* 228 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2)) (* 400 
(* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 272 (* h1 h1 h1) (* h3 h3) h6 j2) (* 64 
(* h1 h1 h1) (* h3 h3) h6) (* 6 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2 j2 j2)) (* 40
 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2 j2)) (* 78 (* h1 h1 h1) h3 (* h4 h4) (* j2 
j2)) (* 60 (* h1 h1 h1) h3 (* h4 h4) j2) (* 16 (* h1 h1 h1) h3 (* h4 h4)) (* 24 
(* h1 h1 h1) h3 h4 h5 (* j2 j2 j2 j2)) (* 160 (* h1 h1 h1) h3 h4 h5 (* j2 j2 j2)
) (* 312 (* h1 h1 h1) h3 h4 h5 (* j2 j2)) (* 240 (* h1 h1 h1) h3 h4 h5 j2) (* 64
 (* h1 h1 h1) h3 h4 h5) (* 3 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 44 (* 
h1 h1 h1) h3 h4 h6 (* j2 j2 j2 j2)) (* 199 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2)) 
(* 342 (* h1 h1 h1) h3 h4 h6 (* j2 j2)) (* 248 (* h1 h1 h1) h3 h4 h6 j2) (* 64 
(* h1 h1 h1) h3 h4 h6) (* 6 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 64 
(* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 238 (* h1 h1 h1) h3 (* h5 h5) (* 
j2 j2 j2)) (* 372 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2)) (* 256 (* h1 h1 h1) h3 
(* h5 h5) j2) (* 64 (* h1 h1 h1) h3 (* h5 h5)) (* 12 (* h1 h1 h1) h3 h5 h6 (* j2
 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2)) (* 476 (* h1 h1 h1)
 h3 h5 h6 (* j2 j2 j2)) (* 744 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) (* 512 (* h1 h1 
h1) h3 h5 h6 j2) (* 128 (* h1 h1 h1) h3 h5 h6) (* 6 (* h1 h1 h1) h3 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 238 (* 
h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2)) (* 372 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2))
 (* 256 (* h1 h1 h1) h3 (* h6 h6) j2) (* 64 (* h1 h1 h1) h3 (* h6 h6)) (* 4 (* 
h1 h1 h1) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2
 j2)) (* 60 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2)) (* 52 (* h1 h1 h1) (* h4 h4) h5
 j2) (* 16 (* h1 h1 h1) (* h4 h4) h5) (* 2 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 22 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 86 (* h1 h1 h1) h4 
(* h5 h5) (* j2 j2 j2)) (* 146 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2)) (* 112 (* h1
 h1 h1) h4 (* h5 h5) j2) (* 32 (* h1 h1 h1) h4 (* h5 h5)) (* 4 (* h1 h1 h1) h4 
h5 h6 (* j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h4 h5 h6 (* j2 j2 j2 j2)) (* 172 
(* h1 h1 h1) h4 h5 h6 (* j2 j2 j2)) (* 292 (* h1 h1 h1) h4 h5 h6 (* j2 j2)) (* 
224 (* h1 h1 h1) h4 h5 h6 j2) (* 64 (* h1 h1 h1) h4 h5 h6) (* (* h1 h1 h1) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 87 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 245 (* h1 h1 h1) (* h5 h5
) h6 (* j2 j2 j2)) (* 348 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 240 (* h1 h1 
h1) (* h5 h5) h6 j2) (* 64 (* h1 h1 h1) (* h5 h5) h6) (* (* h1 h1 h1) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 87 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 245 (* h1 h1 h1) h5 (* h6 h6
) (* j2 j2 j2)) (* 348 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) (* 240 (* h1 h1 h1) 
h5 (* h6 h6) j2) (* 64 (* h1 h1 h1) h5 (* h6 h6)) (* (* h1 h1) (* h2 h2 h2) h5 
(* j2 j2 j2)) (* 5 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2)) (* 8 (* h1 h1) (* h2 h2 
h2) h5 j2) (* 4 (* h1 h1) (* h2 h2 h2) h5) (* (* h1 h1) (* h2 h2 h2) h6 (* j2 j2
 j2)) (* 5 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) h6 
j2) (* 4 (* h1 h1) (* h2 h2 h2) h6) (* (* h1 h1) (* h2 h2) h3 h4 (* j2 j2 j2 j2)
) (* 10 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2 j2)) (* 25 (* h1 h1) (* h2 h2) h3 h4 
(* j2 j2)) (* 20 (* h1 h1) (* h2 h2) h3 h4 j2) (* 4 (* h1 h1) (* h2 h2) h3 h4) 
(* 3 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) h3 h5 
(* j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2)) (* 76 (* h1 h1) (* h2 
h2) h3 h5 j2) (* 20 (* h1 h1) (* h2 h2) h3 h5) (* 3 (* h1 h1) (* h2 h2) h3 h6 
(* j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2 j2)) (* 85 (* h1 h1) 
(* h2 h2) h3 h6 (* j2 j2)) (* 76 (* h1 h1) (* h2 h2) h3 h6 j2) (* 20 (* h1 h1) 
(* h2 h2) h3 h6) (* 3 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2 j2 j2)) (* 26 (* h1 h1)
 (* h2 h2) h4 h5 (* j2 j2 j2)) (* 71 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2)) (* 76 
(* h1 h1) (* h2 h2) h4 h5 j2) (* 28 (* h1 h1) (* h2 h2) h4 h5) (* 2 (* h1 h1) 
(* h2 h2) h4 h6 (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2 j2)) 
(* 42 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2)) (* 44 (* h1 h1) (* h2 h2) h4 h6 j2) 
(* 16 (* h1 h1) (* h2 h2) h4 h6) (* 2 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2 
j2)) (* 16 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2)
 (* h5 h5) (* j2 j2)) (* 44 (* h1 h1) (* h2 h2) (* h5 h5) j2) (* 16 (* h1 h1) 
(* h2 h2) (* h5 h5)) (* 4 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 j2 j2)) (* 32 (* h1
 h1) (* h2 h2) h5 h6 (* j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2)) 
(* 88 (* h1 h1) (* h2 h2) h5 h6 j2) (* 32 (* h1 h1) (* h2 h2) h5 h6) (* 2 (* h1 
h1) (* h2 h2) (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h6 h6) (* 
j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2)) (* 44 (* h1 h1) (* h2 
h2) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h6 h6)) (* 12 (* h1 h1) h2 (* h3 
h3) h4 (* j2 j2 j2 j2)) (* 83 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2 j2)) (* 131 (* 
h1 h1) h2 (* h3 h3) h4 (* j2 j2)) (* 72 (* h1 h1) h2 (* h3 h3) h4 j2) (* 12 (* 
h1 h1) h2 (* h3 h3) h4) (* 24 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2)) (* 160 
(* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2)) (* 264 (* h1 h1) h2 (* h3 h3) h5 (* j2 
j2)) (* 160 (* h1 h1) h2 (* h3 h3) h5 j2) (* 32 (* h1 h1) h2 (* h3 h3) h5) (* 24
 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2)) (* 160 (* h1 h1) h2 (* h3 h3) h6 (* 
j2 j2 j2)) (* 264 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 160 (* h1 h1) h2 (* h3
 h3) h6 j2) (* 32 (* h1 h1) h2 (* h3 h3) h6) (* 8 (* h1 h1) h2 h3 (* h4 h4) (* 
j2 j2 j2 j2)) (* 52 (* h1 h1) h2 h3 (* h4 h4) (* j2 j2 j2)) (* 96 (* h1 h1) h2 
h3 (* h4 h4) (* j2 j2)) (* 68 (* h1 h1) h2 h3 (* h4 h4) j2) (* 16 (* h1 h1) h2 
h3 (* h4 h4)) (* 2 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 47 (* h1 h1) h2 
h3 h4 h5 (* j2 j2 j2 j2)) (* 248 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2)) (* 447 (* 
h1 h1) h2 h3 h4 h5 (* j2 j2)) (* 328 (* h1 h1) h2 h3 h4 h5 j2) (* 84 (* h1 h1) 
h2 h3 h4 h5) (* 2 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 44 (* h1 h1) h2 
h3 h4 h6 (* j2 j2 j2 j2)) (* 218 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2)) (* 376 (* 
h1 h1) h2 h3 h4 h6 (* j2 j2)) (* 264 (* h1 h1) h2 h3 h4 h6 j2) (* 64 (* h1 h1) 
h2 h3 h4 h6) (* 3 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 40 (* h1 h1) 
h2 h3 (* h5 h5) (* j2 j2 j2 j2)) (* 171 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2)) 
(* 282 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2)) (* 196 (* h1 h1) h2 h3 (* h5 h5) j2)
 (* 48 (* h1 h1) h2 h3 (* h5 h5)) (* 6 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2))
 (* 80 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2)) (* 342 (* h1 h1) h2 h3 h5 h6 (* j2
 j2 j2)) (* 564 (* h1 h1) h2 h3 h5 h6 (* j2 j2)) (* 392 (* h1 h1) h2 h3 h5 h6 j2
) (* 96 (* h1 h1) h2 h3 h5 h6) (* 3 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 40 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2)) (* 171 (* h1 h1) h2 h3 (* h6 
h6) (* j2 j2 j2)) (* 282 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2)) (* 196 (* h1 h1) 
h2 h3 (* h6 h6) j2) (* 48 (* h1 h1) h2 h3 (* h6 h6)) (* 8 (* h1 h1) h2 (* h4 h4)
 h5 (* j2 j2 j2 j2)) (* 52 (* h1 h1) h2 (* h4 h4) h5 (* j2 j2 j2)) (* 108 (* h1 
h1) h2 (* h4 h4) h5 (* j2 j2)) (* 92 (* h1 h1) h2 (* h4 h4) h5 j2) (* 28 (* h1 
h1) h2 (* h4 h4) h5) (* 2 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 10 (* h1
 h1) h2 (* h4 h4) h6 (* j2 j2 j2)) (* 18 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2)) 
(* 14 (* h1 h1) h2 (* h4 h4) h6 j2) (* 4 (* h1 h1) h2 (* h4 h4) h6) (* 3 (* h1 
h1) h2 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 33 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2
 j2 j2)) (* 129 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2 j2)) (* 219 (* h1 h1) h2 h4 
(* h5 h5) (* j2 j2)) (* 168 (* h1 h1) h2 h4 (* h5 h5) j2) (* 48 (* h1 h1) h2 h4 
(* h5 h5)) (* 4 (* h1 h1) h2 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 50 (* h1 h1) h2 h4 
h5 h6 (* j2 j2 j2 j2)) (* 210 (* h1 h1) h2 h4 h5 h6 (* j2 j2 j2)) (* 370 (* h1 
h1) h2 h4 h5 h6 (* j2 j2)) (* 290 (* h1 h1) h2 h4 h5 h6 j2) (* 84 (* h1 h1) h2 
h4 h5 h6) (* (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11 (* h1 h1) h2 h4
 (* h6 h6) (* j2 j2 j2 j2)) (* 39 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2)) (* 61 
(* h1 h1) h2 h4 (* h6 h6) (* j2 j2)) (* 44 (* h1 h1) h2 h4 (* h6 h6) j2) (* 12 
(* h1 h1) h2 h4 (* h6 h6)) (* (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9
 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 29 (* h1 h1) h2 (* h5 h5 h5) (* 
j2 j2 j2)) (* 43 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2)) (* 30 (* h1 h1) h2 (* h5 
h5 h5) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5)) (* 4 (* h1 h1) h2 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 42 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 158 (* h1 h1) 
h2 (* h5 h5) h6 (* j2 j2 j2)) (* 262 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2)) (* 198
 (* h1 h1) h2 (* h5 h5) h6 j2) (* 56 (* h1 h1) h2 (* h5 h5) h6) (* 4 (* h1 h1) 
h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 42 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 158 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2)) (* 262 (* h1 h1) h2 h5 (* h6
 h6) (* j2 j2)) (* 198 (* h1 h1) h2 h5 (* h6 h6) j2) (* 56 (* h1 h1) h2 h5 (* h6
 h6)) (* (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h2 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 29 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2)) (* 43 (* 
h1 h1) h2 (* h6 h6 h6) (* j2 j2)) (* 30 (* h1 h1) h2 (* h6 h6 h6) j2) (* 8 (* h1
 h1) h2 (* h6 h6 h6)) (* 18 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 60 (* 
h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2)) (* 74 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2)) 
(* 40 (* h1 h1) (* h3 h3 h3) h4 j2) (* 8 (* h1 h1) (* h3 h3 h3) h4) (* 36 (* h1 
h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 120 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 
j2)) (* 148 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) h5
 j2) (* 16 (* h1 h1) (* h3 h3 h3) h5) (* 36 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 
j2 j2)) (* 120 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 148 (* h1 h1) (* h3 h3
 h3) h6 (* j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) h6 j2) (* 16 (* h1 h1) (* h3 h3 
h3) h6) (* 3 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 38 (* h1 h1) 
(* h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 111 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 
j2 j2)) (* 136 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2)) (* 76 (* h1 h1) (* h3 h3
) (* h4 h4) j2) (* 16 (* h1 h1) (* h3 h3) (* h4 h4)) (* 12 (* h1 h1) (* h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2)) (* 134 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 
384 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 470 (* h1 h1) (* h3 h3) h4 h5 (* 
j2 j2)) (* 264 (* h1 h1) (* h3 h3) h4 h5 j2) (* 56 (* h1 h1) (* h3 h3) h4 h5) 
(* 12 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 122 (* h1 h1) (* h3 h3) 
h4 h6 (* j2 j2 j2 j2)) (* 340 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 410 (* 
h1 h1) (* h3 h3) h4 h6 (* j2 j2)) (* 228 (* h1 h1) (* h3 h3) h4 h6 j2) (* 48 (* 
h1 h1) (* h3 h3) h4 h6) (* 12 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 92 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 236 (* h1 h1) (* h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 276 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2)) (* 152 
(* h1 h1) (* h3 h3) (* h5 h5) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5)) (* 24 (* 
h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 184 (* h1 h1) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2)) (* 472 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 552 (* h1 h1) 
(* h3 h3) h5 h6 (* j2 j2)) (* 304 (* h1 h1) (* h3 h3) h5 h6 j2) (* 64 (* h1 h1) 
(* h3 h3) h5 h6) (* 12 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 92 
(* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 236 (* h1 h1) (* h3 h3) (* h6 
h6) (* j2 j2 j2)) (* 276 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 152 (* h1 
h1) (* h3 h3) (* h6 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h6 h6)) (* 6 (* h1 h1) 
h3 (* h4 h4 h4) (* j2 j2 j2 j2)) (* 22 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2 j2)) 
(* 30 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2)) (* 18 (* h1 h1) h3 (* h4 h4 h4) j2) 
(* 4 (* h1 h1) h3 (* h4 h4 h4)) (* 4 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2
)) (* 54 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 170 (* h1 h1) h3 (* h4 h4
) h5 (* j2 j2 j2)) (* 226 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2)) (* 138 (* h1 h1) 
h3 (* h4 h4) h5 j2) (* 32 (* h1 h1) h3 (* h4 h4) h5) (* 3 (* h1 h1) h3 (* h4 h4)
 h6 (* j2 j2 j2 j2 j2)) (* 41 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 125 
(* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2)) (* 159 (* h1 h1) h3 (* h4 h4) h6 (* j2 
j2)) (* 92 (* h1 h1) h3 (* h4 h4) h6 j2) (* 20 (* h1 h1) h3 (* h4 h4) h6) (* (* 
h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 155 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 381 (* 
h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 448 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2))
 (* 254 (* h1 h1) h3 h4 (* h5 h5) j2) (* 56 (* h1 h1) h3 h4 (* h5 h5)) (* 2 (* 
h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 41 (* h1 h1) h3 h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 253 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 629 (* h1 h1) h3 h4 
h5 h6 (* j2 j2 j2)) (* 749 (* h1 h1) h3 h4 h5 h6 (* j2 j2)) (* 430 (* h1 h1) h3 
h4 h5 h6 j2) (* 96 (* h1 h1) h3 h4 h5 h6) (* 9 (* h1 h1) h3 h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 81 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 221 (* h1 h1) 
h3 h4 (* h6 h6) (* j2 j2 j2)) (* 267 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2)) (* 150
 (* h1 h1) h3 h4 (* h6 h6) j2) (* 32 (* h1 h1) h3 h4 (* h6 h6)) (* 6 (* h1 h1) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 46 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 118 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 138 (* h1 h1) h3 (* h5 h5
 h5) (* j2 j2)) (* 76 (* h1 h1) h3 (* h5 h5 h5) j2) (* 16 (* h1 h1) h3 (* h5 h5 
h5)) (* 3 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 208 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 466 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 525 (* h1 h1) h3 (* h5 h5) 
h6 (* j2 j2)) (* 292 (* h1 h1) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1) h3 (* h5 h5) 
h6) (* 3 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 208 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 466 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 525 (* h1 h1) h3 h5 (* h6 h6) 
(* j2 j2)) (* 292 (* h1 h1) h3 h5 (* h6 h6) j2) (* 64 (* h1 h1) h3 h5 (* h6 h6))
 (* 6 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 46 (* h1 h1) h3 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 118 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 138 (* h1
 h1) h3 (* h6 h6 h6) (* j2 j2)) (* 76 (* h1 h1) h3 (* h6 h6 h6) j2) (* 16 (* h1 
h1) h3 (* h6 h6 h6)) (* 4 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 16 (* h1
 h1) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2)) 
(* 16 (* h1 h1) (* h4 h4 h4) h5 j2) (* 4 (* h1 h1) (* h4 h4 h4) h5) (* 4 (* h1 
h1) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 112 (* h1 
h1) (* h4 h4) (* h5 h5) (* j2 j2)) (* 68 (* h1 h1) (* h4 h4) (* h5 h5) j2) (* 16
 (* h1 h1) (* h4 h4) (* h5 h5)) (* 4 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
)) (* 36 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 104 (* h1 h1) (* h4 h4) 
h5 h6 (* j2 j2 j2)) (* 136 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2)) (* 84 (* h1 h1) 
(* h4 h4) h5 h6 j2) (* 20 (* h1 h1) (* h4 h4) h5 h6) (* 2 (* h1 h1) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 44 
(* h1 h1) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 56 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2
)) (* 34 (* h1 h1) h4 (* h5 h5 h5) j2) (* 8 (* h1 h1) h4 (* h5 h5 h5)) (* 2 (* 
h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 320 (* 
h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 370 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2))
 (* 212 (* h1 h1) h4 (* h5 h5) h6 j2) (* 48 (* h1 h1) h4 (* h5 h5) h6) (* (* h1 
h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 86 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 204 (* h1 h1)
 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 241 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2)) (* 
140 (* h1 h1) h4 h5 (* h6 h6) j2) (* 32 (* h1 h1) h4 h5 (* h6 h6)) (* (* h1 h1) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 54 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 116 (* h1 h1) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 129 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 72 (* 
h1 h1) (* h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h5 h5 h5) h6) (* 2 (* h1 h1) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 108 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 232 (* h1
 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 258 (* h1 h1) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 144 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h5 h5) (* h6
 h6)) (* (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 54 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 116 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 129 (* h1 h1) h5 (* h6 h6 h6) 
(* j2 j2)) (* 72 (* h1 h1) h5 (* h6 h6 h6) j2) (* 16 (* h1 h1) h5 (* h6 h6 h6)) 
(* h1 (* h2 h2 h2) h3 h4 (* j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 h4 (* j2 j2)) (* 
2 h1 (* h2 h2 h2) h3 h4 j2) (* 2 h1 (* h2 h2 h2) h3 h5 (* j2 j2 j2)) (* 6 h1 (* 
h2 h2 h2) h3 h5 (* j2 j2)) (* 4 h1 (* h2 h2 h2) h3 h5 j2) (* 2 h1 (* h2 h2 h2) 
h3 h6 (* j2 j2 j2)) (* 6 h1 (* h2 h2 h2) h3 h6 (* j2 j2)) (* 4 h1 (* h2 h2 h2) 
h3 h6 j2) (* 2 h1 (* h2 h2 h2) h4 h5 (* j2 j2 j2)) (* 8 h1 (* h2 h2 h2) h4 h5 
(* j2 j2)) (* 10 h1 (* h2 h2 h2) h4 h5 j2) (* 4 h1 (* h2 h2 h2) h4 h5) (* h1 (* 
h2 h2 h2) h4 h6 (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h4 h6 (* j2 j2)) (* 5 h1 (* 
h2 h2 h2) h4 h6 j2) (* 2 h1 (* h2 h2 h2) h4 h6) (* h1 (* h2 h2 h2) (* h5 h5) (* 
j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2)) (* 5 h1 (* h2 h2 h2) (* h5 
h5) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5)) (* 2 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2))
 (* 8 h1 (* h2 h2 h2) h5 h6 (* j2 j2)) (* 10 h1 (* h2 h2 h2) h5 h6 j2) (* 4 h1 
(* h2 h2 h2) h5 h6) (* h1 (* h2 h2 h2) (* h6 h6) (* j2 j2 j2)) (* 4 h1 (* h2 h2 
h2) (* h6 h6) (* j2 j2)) (* 5 h1 (* h2 h2 h2) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2)
 (* h6 h6)) (* 2 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2 j2 j2)) (* 18 h1 (* h2 h2) 
(* h3 h3) h4 (* j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2)) (* 8 h1 
(* h2 h2) (* h3 h3) h4 j2) (* 3 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 25
 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 34 h1 (* h2 h2) (* h3 h3) h5 (* j2 
j2)) (* 12 h1 (* h2 h2) (* h3 h3) h5 j2) (* 3 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2
 j2 j2)) (* 25 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 34 h1 (* h2 h2) (* h3 
h3) h6 (* j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3) h6 j2) (* 2 h1 (* h2 h2) h3 (* h4
 h4) (* j2 j2 j2 j2)) (* 15 h1 (* h2 h2) h3 (* h4 h4) (* j2 j2 j2)) (* 26 h1 (* 
h2 h2) h3 (* h4 h4) (* j2 j2)) (* 15 h1 (* h2 h2) h3 (* h4 h4) j2) (* 2 h1 (* h2
 h2) h3 (* h4 h4)) (* 7 h1 (* h2 h2) h3 h4 h5 (* j2 j2 j2 j2)) (* 52 h1 (* h2 h2
) h3 h4 h5 (* j2 j2 j2)) (* 99 h1 (* h2 h2) h3 h4 h5 (* j2 j2)) (* 70 h1 (* h2 
h2) h3 h4 h5 j2) (* 16 h1 (* h2 h2) h3 h4 h5) (* 6 h1 (* h2 h2) h3 h4 h6 (* j2 
j2 j2 j2)) (* 43 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2)) (* 78 h1 (* h2 h2) h3 h4 h6
 (* j2 j2)) (* 51 h1 (* h2 h2) h3 h4 h6 j2) (* 10 h1 (* h2 h2) h3 h4 h6) (* 4 h1
 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 28 h1 (* h2 h2) h3 (* h5 h5) (* j2 
j2 j2)) (* 52 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2)) (* 36 h1 (* h2 h2) h3 (* h5 
h5) j2) (* 8 h1 (* h2 h2) h3 (* h5 h5)) (* 8 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 
j2)) (* 56 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 104 h1 (* h2 h2) h3 h5 h6 (* 
j2 j2)) (* 72 h1 (* h2 h2) h3 h5 h6 j2) (* 16 h1 (* h2 h2) h3 h5 h6) (* 4 h1 (* 
h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 28 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2
)) (* 52 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 36 h1 (* h2 h2) h3 (* h6 h6) j2
) (* 8 h1 (* h2 h2) h3 (* h6 h6)) (* 3 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2 j2 j2)
) (* 21 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2 j2)) (* 45 h1 (* h2 h2) (* h4 h4) h5 
(* j2 j2)) (* 39 h1 (* h2 h2) (* h4 h4) h5 j2) (* 12 h1 (* h2 h2) (* h4 h4) h5) 
(* h1 (* h2 h2) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 5 h1 (* h2 h2) (* h4 h4) h6 (* 
j2 j2 j2)) (* 9 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2)) (* 7 h1 (* h2 h2) (* h4 h4)
 h6 j2) (* 2 h1 (* h2 h2) (* h4 h4) h6) (* 4 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 
j2 j2)) (* 26 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 j2)) (* 54 h1 (* h2 h2) h4 (* 
h5 h5) (* j2 j2)) (* 46 h1 (* h2 h2) h4 (* h5 h5) j2) (* 14 h1 (* h2 h2) h4 (* 
h5 h5)) (* 7 h1 (* h2 h2) h4 h5 h6 (* j2 j2 j2 j2)) (* 47 h1 (* h2 h2) h4 h5 h6 
(* j2 j2 j2)) (* 99 h1 (* h2 h2) h4 h5 h6 (* j2 j2)) (* 85 h1 (* h2 h2) h4 h5 h6
 j2) (* 26 h1 (* h2 h2) h4 h5 h6) (* 2 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2 j2)
) (* 10 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2)) (* 18 h1 (* h2 h2) h4 (* h6 h6) 
(* j2 j2)) (* 14 h1 (* h2 h2) h4 (* h6 h6) j2) (* 4 h1 (* h2 h2) h4 (* h6 h6)) 
(* h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5 h1 (* h2 h2) (* h5 h5 h5) (* 
j2 j2 j2)) (* 9 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2)) (* 7 h1 (* h2 h2) (* h5 h5 
h5) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5)) (* 4 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 26 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 54 h1 (* h2 h2) (* h5 
h5) h6 (* j2 j2)) (* 46 h1 (* h2 h2) (* h5 h5) h6 j2) (* 14 h1 (* h2 h2) (* h5 
h5) h6) (* 4 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 26 h1 (* h2 h2) h5 
(* h6 h6) (* j2 j2 j2)) (* 54 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2)) (* 46 h1 (* 
h2 h2) h5 (* h6 h6) j2) (* 14 h1 (* h2 h2) h5 (* h6 h6)) (* h1 (* h2 h2) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 5 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2)) (* 9 h1 (* 
h2 h2) (* h6 h6 h6) (* j2 j2)) (* 7 h1 (* h2 h2) (* h6 h6 h6) j2) (* 2 h1 (* h2 
h2) (* h6 h6 h6)) (* 9 h1 h2 (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 24 h1 h2 (* h3 
h3 h3) h4 (* j2 j2 j2)) (* 21 h1 h2 (* h3 h3 h3) h4 (* j2 j2)) (* 6 h1 h2 (* h3 
h3 h3) h4 j2) (* 12 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3 
h3) h5 (* j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3) h5 (* j2 j2)) (* 8 h1 h2 (* h3 h3 
h3) h5 j2) (* 12 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3 h3)
 h6 (* j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3) h6 (* j2 j2)) (* 8 h1 h2 (* h3 h3 h3)
 h6 j2) (* h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 18 h1 h2 (* h3 h3) 
(* h4 h4) (* j2 j2 j2 j2)) (* 51 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2)) (* 56 
h1 h2 (* h3 h3) (* h4 h4) (* j2 j2)) (* 26 h1 h2 (* h3 h3) (* h4 h4) j2) (* 4 h1
 h2 (* h3 h3) (* h4 h4)) (* 4 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 57 h1
 h2 (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 166 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2)) 
(* 197 h1 h2 (* h3 h3) h4 h5 (* j2 j2)) (* 104 h1 h2 (* h3 h3) h4 h5 j2) (* 20 
h1 h2 (* h3 h3) h4 h5) (* 4 h1 h2 (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 50 h1 
h2 (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 139 h1 h2 (* h3 h3) h4 h6 (* j2 j2 j2)) 
(* 158 h1 h2 (* h3 h3) h4 h6 (* j2 j2)) (* 79 h1 h2 (* h3 h3) h4 h6 j2) (* 14 h1
 h2 (* h3 h3) h4 h6) (* 3 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 32 h1
 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 88 h1 h2 (* h3 h3) (* h5 h5) (* j2 
j2 j2)) (* 102 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 53 h1 h2 (* h3 h3) (* h5 
h5) j2) (* 10 h1 h2 (* h3 h3) (* h5 h5)) (* 6 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 
j2 j2)) (* 64 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 176 h1 h2 (* h3 h3) h5 
h6 (* j2 j2 j2)) (* 204 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 106 h1 h2 (* h3 h3) 
h5 h6 j2) (* 20 h1 h2 (* h3 h3) h5 h6) (* 3 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 32 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 88 h1 h2 (* h3 h3
) (* h6 h6) (* j2 j2 j2)) (* 102 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2)) (* 53 h1 
h2 (* h3 h3) (* h6 h6) j2) (* 10 h1 h2 (* h3 h3) (* h6 h6)) (* 5 h1 h2 h3 (* h4 
h4 h4) (* j2 j2 j2 j2)) (* 17 h1 h2 h3 (* h4 h4 h4) (* j2 j2 j2)) (* 21 h1 h2 h3
 (* h4 h4 h4) (* j2 j2)) (* 11 h1 h2 h3 (* h4 h4 h4) j2) (* 2 h1 h2 h3 (* h4 h4 
h4)) (* 4 h1 h2 h3 (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 47 h1 h2 h3 (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 143 h1 h2 h3 (* h4 h4) h5 (* j2 j2 j2)) (* 187 h1 h2 h3 (* 
h4 h4) h5 (* j2 j2)) (* 113 h1 h2 h3 (* h4 h4) h5 j2) (* 26 h1 h2 h3 (* h4 h4) 
h5) (* 2 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 29 h1 h2 h3 (* h4 h4) h6 
(* j2 j2 j2 j2)) (* 85 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2)) (* 101 h1 h2 h3 (* h4
 h4) h6 (* j2 j2)) (* 53 h1 h2 h3 (* h4 h4) h6 j2) (* 10 h1 h2 h3 (* h4 h4) h6) 
(* 7 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 64 h1 h2 h3 h4 (* h5 h5) (* j2
 j2 j2 j2)) (* 180 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2)) (* 226 h1 h2 h3 h4 (* h5 
h5) (* j2 j2)) (* 133 h1 h2 h3 h4 (* h5 h5) j2) (* 30 h1 h2 h3 h4 (* h5 h5)) (* 
12 h1 h2 h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 114 h1 h2 h3 h4 h5 h6 (* j2 j2 j2 j2
)) (* 326 h1 h2 h3 h4 h5 h6 (* j2 j2 j2)) (* 414 h1 h2 h3 h4 h5 h6 (* j2 j2)) 
(* 246 h1 h2 h3 h4 h5 h6 j2) (* 56 h1 h2 h3 h4 h5 h6) (* 4 h1 h2 h3 h4 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 43 h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 119 h1 h2 
h3 h4 (* h6 h6) (* j2 j2 j2)) (* 139 h1 h2 h3 h4 (* h6 h6) (* j2 j2)) (* 73 h1 
h2 h3 h4 (* h6 h6) j2) (* 14 h1 h2 h3 h4 (* h6 h6)) (* 2 h1 h2 h3 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 19 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 51 h1 h2 h3 
(* h5 h5 h5) (* j2 j2 j2)) (* 59 h1 h2 h3 (* h5 h5 h5) (* j2 j2)) (* 31 h1 h2 h3
 (* h5 h5 h5) j2) (* 6 h1 h2 h3 (* h5 h5 h5)) (* 8 h1 h2 h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 67 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 183 h1 h2 h3 (* h5
 h5) h6 (* j2 j2 j2)) (* 227 h1 h2 h3 (* h5 h5) h6 (* j2 j2)) (* 133 h1 h2 h3 
(* h5 h5) h6 j2) (* 30 h1 h2 h3 (* h5 h5) h6) (* 8 h1 h2 h3 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 67 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 183 h1 h2 h3 h5 
(* h6 h6) (* j2 j2 j2)) (* 227 h1 h2 h3 h5 (* h6 h6) (* j2 j2)) (* 133 h1 h2 h3 
h5 (* h6 h6) j2) (* 30 h1 h2 h3 h5 (* h6 h6)) (* 2 h1 h2 h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 19 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 51 h1 h2 h3 (* h6 
h6 h6) (* j2 j2 j2)) (* 59 h1 h2 h3 (* h6 h6 h6) (* j2 j2)) (* 31 h1 h2 h3 (* h6
 h6 h6) j2) (* 6 h1 h2 h3 (* h6 h6 h6)) (* 4 h1 h2 (* h4 h4 h4) h5 (* j2 j2 j2 
j2)) (* 16 h1 h2 (* h4 h4 h4) h5 (* j2 j2 j2)) (* 24 h1 h2 (* h4 h4 h4) h5 (* j2
 j2)) (* 16 h1 h2 (* h4 h4 h4) h5 j2) (* 4 h1 h2 (* h4 h4 h4) h5) (* 3 h1 h2 (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 74 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 96 h1 h2 (* h4 h4) (* h5 
h5) (* j2 j2)) (* 59 h1 h2 (* h4 h4) (* h5 h5) j2) (* 14 h1 h2 (* h4 h4) (* h5 
h5)) (* 2 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 76 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 104 h1 h2 (* h4 h4
) h5 h6 (* j2 j2)) (* 66 h1 h2 (* h4 h4) h5 h6 j2) (* 16 h1 h2 (* h4 h4) h5 h6) 
(* 2 h1 h2 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16 h1 h2 h4 (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 44 h1 h2 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 56 h1 h2 h4 (* h5 h5 h5
) (* j2 j2)) (* 34 h1 h2 h4 (* h5 h5 h5) j2) (* 8 h1 h2 h4 (* h5 h5 h5)) (* 7 h1
 h2 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 58 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 162 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 208 h1 h2 h4 (* h5 h5) h6 (* 
j2 j2)) (* 127 h1 h2 h4 (* h5 h5) h6 j2) (* 30 h1 h2 h4 (* h5 h5) h6) (* 4 h1 h2
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 36 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 104 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 136 h1 h2 h4 h5 (* h6 h6) (* j2 
j2)) (* 84 h1 h2 h4 h5 (* h6 h6) j2) (* 20 h1 h2 h4 h5 (* h6 h6)) (* 2 h1 h2 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 44 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 56 h1 h2 (* h5 h5 h5) h6 (* j2 j2))
 (* 34 h1 h2 (* h5 h5 h5) h6 j2) (* 8 h1 h2 (* h5 h5 h5) h6) (* 4 h1 h2 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 88 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 112 h1 h2 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 68 h1 h2 (* h5 h5) (* h6 h6) j2) (* 16 h1 h2 (* h5 h5) (* h6 h6)) 
(* 2 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 h2 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 44 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 56 h1 h2 h5 (* h6 h6 h6
) (* j2 j2)) (* 34 h1 h2 h5 (* h6 h6 h6) j2) (* 8 h1 h2 h5 (* h6 h6 h6)) (* 3 h1
 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3 h3) (* h4 h4) (* 
j2 j2 j2 j2)) (* 26 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) (* 24 h1 (* h3 h3 h3
) (* h4 h4) (* j2 j2)) (* 11 h1 (* h3 h3 h3) (* h4 h4) j2) (* 2 h1 (* h3 h3 h3) 
(* h4 h4)) (* 12 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 56 h1 (* h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2)) (* 104 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 96 h1 (* 
h3 h3 h3) h4 h5 (* j2 j2)) (* 44 h1 (* h3 h3 h3) h4 h5 j2) (* 8 h1 (* h3 h3 h3) 
h4 h5) (* 9 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 42 h1 (* h3 h3 h3) h4 
h6 (* j2 j2 j2 j2)) (* 78 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 72 h1 (* h3 h3 
h3) h4 h6 (* j2 j2)) (* 33 h1 (* h3 h3 h3) h4 h6 j2) (* 6 h1 (* h3 h3 h3) h4 h6)
 (* 6 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2)) (* 52 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 48 h1 (* 
h3 h3 h3) (* h5 h5) (* j2 j2)) (* 22 h1 (* h3 h3 h3) (* h5 h5) j2) (* 4 h1 (* h3
 h3 h3) (* h5 h5)) (* 12 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 56 h1 (* 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 104 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 
96 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 44 h1 (* h3 h3 h3) h5 h6 j2) (* 8 h1 (* 
h3 h3 h3) h5 h6) (* 6 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 h1 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 52 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2
)) (* 48 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 22 h1 (* h3 h3 h3) (* h6 h6) j2
) (* 4 h1 (* h3 h3 h3) (* h6 h6)) (* 3 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2 j2 
j2)) (* 14 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2 j2)) (* 26 h1 (* h3 h3) (* h4 
h4 h4) (* j2 j2 j2)) (* 24 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2)) (* 11 h1 (* h3 
h3) (* h4 h4 h4) j2) (* 2 h1 (* h3 h3) (* h4 h4 h4)) (* h1 (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 22 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 92 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 168 h1 (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 157 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 74 h1 (* h3 h3) 
(* h4 h4) h5 j2) (* 14 h1 (* h3 h3) (* h4 h4) h5) (* 12 h1 (* h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2)) (* 56 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 104 
h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 96 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2
)) (* 44 h1 (* h3 h3) (* h4 h4) h6 j2) (* 8 h1 (* h3 h3) (* h4 h4) h6) (* 2 h1 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 29 h1 (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 112 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 198 h1 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 182 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2))
 (* 85 h1 (* h3 h3) h4 (* h5 h5) j2) (* 16 h1 (* h3 h3) h4 (* h5 h5)) (* 4 h1 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 55 h1 (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 210 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 370 h1 (* h3 h3) h4 
h5 h6 (* j2 j2 j2)) (* 340 h1 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 159 h1 (* h3 h3) 
h4 h5 h6 j2) (* 30 h1 (* h3 h3) h4 h5 h6) (* 15 h1 (* h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 70 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 130 h1 (* h3 
h3) h4 (* h6 h6) (* j2 j2 j2)) (* 120 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 55
 h1 (* h3 h3) h4 (* h6 h6) j2) (* 10 h1 (* h3 h3) h4 (* h6 h6)) (* 6 h1 (* h3 h3
) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 52 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 48 h1 (* h3 h3) (* h5 h5 
h5) (* j2 j2)) (* 22 h1 (* h3 h3) (* h5 h5 h5) j2) (* 4 h1 (* h3 h3) (* h5 h5 h5
)) (* 3 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 33 h1 (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 118 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 202 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 183 h1 (* h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 85 h1 (* h3 h3) (* h5 h5) h6 j2) (* 16 h1 (* h3 h3) (* h5 h5) h6) 
(* 3 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 h1 (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 118 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
202 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 183 h1 (* h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 85 h1 (* h3 h3) h5 (* h6 h6) j2) (* 16 h1 (* h3 h3) h5 (* h6 h6)) (* 
6 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 52 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 (* h3 h3
) (* h6 h6 h6) (* j2 j2)) (* 22 h1 (* h3 h3) (* h6 h6 h6) j2) (* 4 h1 (* h3 h3) 
(* h6 h6 h6)) (* 4 h1 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 20 h1 h3 (* h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 40 h1 h3 (* h4 h4 h4) h5 (* j2 j2 j2)) (* 40 h1 h3
 (* h4 h4 h4) h5 (* j2 j2)) (* 20 h1 h3 (* h4 h4 h4) h5 j2) (* 4 h1 h3 (* h4 h4 
h4) h5) (* 2 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 25 h1 h3 (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 94 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
)) (* 166 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 154 h1 h3 (* h4 h4) (* h5 
h5) (* j2 j2)) (* 73 h1 h3 (* h4 h4) (* h5 h5) j2) (* 14 h1 h3 (* h4 h4) (* h5 
h5)) (* 2 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 26 h1 h3 (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2)) (* 100 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 180 h1 
h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 170 h1 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 82 
h1 h3 (* h4 h4) h5 h6 j2) (* 16 h1 h3 (* h4 h4) h5 h6) (* h1 h3 h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 14 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 54 h1 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 96 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) 
(* 89 h1 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 42 h1 h3 h4 (* h5 h5 h5) j2) (* 8 h1 
h3 h4 (* h5 h5 h5)) (* 6 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 61 h1 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 214 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 366 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 334 h1 h3 h4 (* h5 h5) h6 (* 
j2 j2)) (* 157 h1 h3 h4 (* h5 h5) h6 j2) (* 30 h1 h3 h4 (* h5 h5) h6) (* 4 h1 h3
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 140 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 240 h1 h3 h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 220 h1 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 104 h1 h3 h4 h5 (* 
h6 h6) j2) (* 20 h1 h3 h4 h5 (* h6 h6)) (* 2 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 18 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60 h1 h3 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 100 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 90 h1 h3 
(* h5 h5 h5) h6 (* j2 j2)) (* 42 h1 h3 (* h5 h5 h5) h6 j2) (* 8 h1 h3 (* h5 h5 
h5) h6) (* 4 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 h1 h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 120 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 200 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 180 h1 h3 (* h5 h5) (* h6
 h6) (* j2 j2)) (* 84 h1 h3 (* h5 h5) (* h6 h6) j2) (* 16 h1 h3 (* h5 h5) (* h6 
h6)) (* 2 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18 h1 h3 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 60 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 100 h1 
h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 90 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 42 h1
 h3 h5 (* h6 h6 h6) j2) (* 8 h1 h3 h5 (* h6 h6 h6)) (* 2 h1 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 20 
h1 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 20 h1 (* h4 h4 h4) (* h5 h5) (* j2 j2
)) (* 10 h1 (* h4 h4 h4) (* h5 h5) j2) (* 2 h1 (* h4 h4 h4) (* h5 h5)) (* 2 h1 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 20 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 20 h1 (* h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5) j2) (* 2 h1 (* h4 h4) (* h5
 h5 h5)) (* h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13 h1 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 90 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 85 h1 (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 41 h1 (* h4 h4) (* h5 h5) h6 j2) (* 8 h1 (* h4 h4) (* h5 h5) h6) 
(* h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11 h1 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 40 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 70 h1 h4 (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 65 h1 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 31 h1 h4 (* h5
 h5 h5) h6 j2) (* 6 h1 h4 (* h5 h5 h5) h6) (* 2 h1 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 20 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 h1 h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 120 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 110 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 52 h1 h4 (* h5 h5) (* h6 h6)
 j2) (* 10 h1 h4 (* h5 h5) (* h6 h6)) (* h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 9 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 50 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
45 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21 h1 (* h5 h5 h5) (* h6 h6) j2) (* 4
 h1 (* h5 h5 h5) (* h6 h6)) (* h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 9 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 50 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 45 h1 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 21 h1 (* h5 h5) (* h6 h6 h6) j2) (* 4 h1 (* h5
 h5) (* h6 h6 h6)) (* (* h2 h2 h2) (* h3 h3) h4 (* j2 j2 j2)) (* (* h2 h2 h2) 
(* h3 h3) h4 (* j2 j2)) (* (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* (* h2 h2 
h2) (* h3 h3) h5 (* j2 j2)) (* (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* (* h2 
h2 h2) (* h3 h3) h6 (* j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) (* j2 j2 j2)) (* 2 
(* h2 h2 h2) h3 (* h4 h4) (* j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) j2) (* 2 (* h2
 h2 h2) h3 h4 h5 (* j2 j2 j2)) (* 4 (* h2 h2 h2) h3 h4 h5 (* j2 j2)) (* 2 (* h2 
h2 h2) h3 h4 h5 j2) (* 2 (* h2 h2 h2) h3 h4 h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) 
h3 h4 h6 (* j2 j2)) (* 2 (* h2 h2 h2) h3 h4 h6 j2) (* (* h2 h2 h2) h3 (* h5 h5) 
(* j2 j2 j2)) (* 2 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* (* h2 h2 h2) h3 (* h5
 h5) j2) (* 2 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) h3 h5 h6 (* 
j2 j2)) (* 2 (* h2 h2 h2) h3 h5 h6 j2) (* (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)
) (* 2 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* (* h2 h2 h2) h3 (* h6 h6) j2) (* 
(* h2 h2 h2) (* h4 h4) h5 (* j2 j2 j2)) (* 3 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2)
) (* 3 (* h2 h2 h2) (* h4 h4) h5 j2) (* (* h2 h2 h2) (* h4 h4) h5) (* (* h2 h2 
h2) h4 (* h5 h5) (* j2 j2 j2)) (* 3 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2)) (* 3 
(* h2 h2 h2) h4 (* h5 h5) j2) (* (* h2 h2 h2) h4 (* h5 h5)) (* 2 (* h2 h2 h2) h4
 h5 h6 (* j2 j2 j2)) (* 6 (* h2 h2 h2) h4 h5 h6 (* j2 j2)) (* 6 (* h2 h2 h2) h4 
h5 h6 j2) (* 2 (* h2 h2 h2) h4 h5 h6) (* (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2))
 (* 3 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 3 (* h2 h2 h2) (* h5 h5) h6 j2) 
(* (* h2 h2 h2) (* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 3 
(* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) h5 (* h6 h6) j2) (* (* h2
 h2 h2) h5 (* h6 h6)) (* (* h2 h2) (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 2 (* h2 
h2) (* h3 h3 h3) h4 (* j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) h4 (* j2 j2)) (* (* 
h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 
j2)) (* (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* (* h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3
) h6 (* j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 6 (* h2 
h2) (* h3 h3) (* h4 h4) (* j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* h4 h4) (* j2 
j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) j2) (* 4 (* h2 h2) (* h3 h3) h4 h5 (* j2
 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 12 (* h2 h2) (* h3 
h3) h4 h5 (* j2 j2)) (* 4 (* h2 h2) (* h3 h3) h4 h5 j2) (* 4 (* h2 h2) (* h3 h3)
 h4 h6 (* j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 12 (* 
h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 4 (* h2 h2) (* h3 h3) h4 h6 j2) (* 2 (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 2 (* h2 h2) (* h3 h3
) (* h5 h5) j2) (* 4 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 12 (* h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 4 
(* h2 h2) (* h3 h3) h5 h6 j2) (* 2 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)
) (* 6 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* 
h6 h6) (* j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* (* h2 h2) h3 (* h4 
h4 h4) (* j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4 h4) (* j2 j2 j2)) (* 3 (* h2 
h2) h3 (* h4 h4 h4) (* j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4) j2) (* 4 (* h2 h2) 
h3 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 15 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2 j2)) 
(* 21 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2)) (* 13 (* h2 h2) h3 (* h4 h4) h5 j2) 
(* 3 (* h2 h2) h3 (* h4 h4) h5) (* 3 (* h2 h2) h3 (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 9 (* h2 h2) h3 (* h4 h4) h6 (* j2 j2 j2)) (* 9 (* h2 h2) h3 (* h4 h4) h6 (* 
j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4) h6 j2) (* 4 (* h2 h2) h3 h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 15 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 21 (* h2 h2) h3 h4 
(* h5 h5) (* j2 j2)) (* 13 (* h2 h2) h3 h4 (* h5 h5) j2) (* 3 (* h2 h2) h3 h4 
(* h5 h5)) (* 8 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 30 (* h2 h2) h3 h4 h5 
h6 (* j2 j2 j2)) (* 42 (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 26 (* h2 h2) h3 h4 h5
 h6 j2) (* 6 (* h2 h2) h3 h4 h5 h6) (* 3 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 
j2)) (* 9 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 9 (* h2 h2) h3 h4 (* h6 h6)
 (* j2 j2)) (* 3 (* h2 h2) h3 h4 (* h6 h6) j2) (* (* h2 h2) h3 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 3 (* h2 h2) h3 (* 
h5 h5 h5) (* j2 j2)) (* (* h2 h2) h3 (* h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 15 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 21 (* h2 
h2) h3 (* h5 h5) h6 (* j2 j2)) (* 13 (* h2 h2) h3 (* h5 h5) h6 j2) (* 3 (* h2 h2
) h3 (* h5 h5) h6) (* 4 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 15 (* h2 
h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 21 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 
13 (* h2 h2) h3 h5 (* h6 h6) j2) (* 3 (* h2 h2) h3 h5 (* h6 h6)) (* (* h2 h2) h3
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 3
 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* (* h2 h2) h3 (* h6 h6 h6) j2) (* (* h2 
h2) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) h5 (* j2 j2 j2)
) (* 6 (* h2 h2) (* h4 h4 h4) h5 (* j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) h5 j2) 
(* (* h2 h2) (* h4 h4 h4) h5) (* 2 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)
) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) j2) (* 2 (* h2 h2) (* h4 h4
) (* h5 h5)) (* 3 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 12 (* h2 h2) (* 
h4 h4) h5 h6 (* j2 j2 j2)) (* 18 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2)) (* 12 (* 
h2 h2) (* h4 h4) h5 h6 j2) (* 3 (* h2 h2) (* h4 h4) h5 h6) (* (* h2 h2) h4 (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 4 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 6 (* h2
 h2) h4 (* h5 h5 h5) (* j2 j2)) (* 4 (* h2 h2) h4 (* h5 h5 h5) j2) (* (* h2 h2) 
h4 (* h5 h5 h5)) (* 4 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 16 (* h2 h2)
 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 16 
(* h2 h2) h4 (* h5 h5) h6 j2) (* 4 (* h2 h2) h4 (* h5 h5) h6) (* 3 (* h2 h2) h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
18 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 12 (* h2 h2) h4 h5 (* h6 h6) j2) (* 3
 (* h2 h2) h4 h5 (* h6 h6)) (* (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4 
(* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)
) (* 4 (* h2 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5) h6) (* 2 (* h2 h2
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 12 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* h2 h2) (* h5 h5) 
(* h6 h6) j2) (* 2 (* h2 h2) (* h5 h5) (* h6 h6)) (* (* h2 h2) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 4 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2) h5 (* h6 h6 h6) j2) (* (* h2 h2) h5 (* h6
 h6 h6)) (* h2 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3) 
(* h4 h4) (* j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) (* 4 h2 
(* h3 h3 h3) (* h4 h4) (* j2 j2)) (* h2 (* h3 h3 h3) (* h4 h4) j2) (* 2 h2 (* h3
 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 12 h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h4 h5 (* j2 j2)) 
(* 2 h2 (* h3 h3 h3) h4 h5 j2) (* 2 h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 8 h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) h4 h6 (* j2 j2
 j2)) (* 8 h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 2 h2 (* h3 h3 h3) h4 h6 j2) (* h2
 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 4 h2 (* h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* h2 (* h3 h3 h3) (* h5 h5) j2) (* 2 h2 (* h3 h3 h3) h5 h6
 (* j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 12 h2 (* h3 
h3 h3) h5 h6 (* j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 2 h2 (* h3 
h3 h3) h5 h6 j2) (* h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) 
(* 4 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* h2 (* h3 h3 h3) (* h6 h6) j2) (* h2
 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h4 h4 h4) (* j2
 j2 j2 j2)) (* 6 h2 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2)) (* 4 h2 (* h3 h3) (* h4
 h4 h4) (* j2 j2)) (* h2 (* h3 h3) (* h4 h4 h4) j2) (* 4 h2 (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 36 h2
 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 34 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2))
 (* 16 h2 (* h3 h3) (* h4 h4) h5 j2) (* 3 h2 (* h3 h3) (* h4 h4) h5) (* 3 h2 (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3) (* h4 h4) h6 (* j2 j2
 j2 j2)) (* 18 h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 12 h2 (* h3 h3) (* h4 
h4) h6 (* j2 j2)) (* 3 h2 (* h3 h3) (* h4 h4) h6 j2) (* 4 h2 (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 36 
h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 34 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2
)) (* 16 h2 (* h3 h3) h4 (* h5 h5) j2) (* 3 h2 (* h3 h3) h4 (* h5 h5)) (* 8 h2 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 38 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2)) (* 72 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 68 h2 (* h3 h3) h4 h5 h6 (* j2
 j2)) (* 32 h2 (* h3 h3) h4 h5 h6 j2) (* 6 h2 (* h3 h3) h4 h5 h6) (* 3 h2 (* h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2
 j2)) (* 18 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 12 h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2)) (* 3 h2 (* h3 h3) h4 (* h6 h6) j2) (* h2 (* h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6 h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 4 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 
h2 (* h3 h3) (* h5 h5 h5) j2) (* 4 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 19 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 36 h2 (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 34 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 16 h2 (* h3 h3) 
(* h5 h5) h6 j2) (* 3 h2 (* h3 h3) (* h5 h5) h6) (* 4 h2 (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 36 h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 34 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 16 h2 (* h3 h3) h5 (* h6 h6) j2) (* 3 h2 (* h3 h3) h5 (* h6 h6)) (* h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 6 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h2 (* h3 h3) (* h6 h6 h6)
 (* j2 j2)) (* h2 (* h3 h3) (* h6 h6 h6) j2) (* 2 h2 h3 (* h4 h4 h4) h5 (* j2 j2
 j2 j2 j2)) (* 10 h2 h3 (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 20 h2 h3 (* h4 h4 h4
) h5 (* j2 j2 j2)) (* 20 h2 h3 (* h4 h4 h4) h5 (* j2 j2)) (* 10 h2 h3 (* h4 h4 
h4) h5 j2) (* 2 h2 h3 (* h4 h4 h4) h5) (* 4 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 20 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 40 h2 h3 (* h4 h4
) (* h5 h5) (* j2 j2 j2)) (* 40 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 20 h2 h3
 (* h4 h4) (* h5 h5) j2) (* 4 h2 h3 (* h4 h4) (* h5 h5)) (* 6 h2 h3 (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2)) (* 30 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 60 h2 h3
 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 60 h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 30 h2 
h3 (* h4 h4) h5 h6 j2) (* 6 h2 h3 (* h4 h4) h5 h6) (* 2 h2 h3 h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 10 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 20 h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 20 h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 10 h2 h3 h4
 (* h5 h5 h5) j2) (* 2 h2 h3 h4 (* h5 h5 h5)) (* 8 h2 h3 h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 40 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 80 h2 h3 h4 (* h5 
h5) h6 (* j2 j2 j2)) (* 80 h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 40 h2 h3 h4 (* h5
 h5) h6 j2) (* 8 h2 h3 h4 (* h5 h5) h6) (* 6 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 30 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 60 h2 h3 h4 h5 (* h6 h6)
 (* j2 j2 j2)) (* 60 h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 30 h2 h3 h4 h5 (* h6 h6
) j2) (* 6 h2 h3 h4 h5 (* h6 h6)) (* 2 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 10 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20 h2 h3 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 20 h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 10 h2 h3 (* h5 h5 h5) h6 j2) 
(* 2 h2 h3 (* h5 h5 h5) h6) (* 4 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 20 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 h2 h3 (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 40 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 20 h2 h3 (* h5 h5) 
(* h6 h6) j2) (* 4 h2 h3 (* h5 h5) (* h6 h6)) (* 2 h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 10 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 h2 h3 h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 20 h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 10 h2 h3 h5 (* h6
 h6 h6) j2) (* 2 h2 h3 h5 (* h6 h6 h6)) (* h2 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 5 h2 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 10 h2 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 10 h2 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 5 h2 (* h4
 h4 h4) (* h5 h5) j2) (* h2 (* h4 h4 h4) (* h5 h5)) (* h2 (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2)) (* 5 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 10 h2 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 10 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 5 h2 (* h4 h4) (* h5 h5 h5) j2) (* h2 (* h4 h4) (* h5 h5 h5)) (* 3 h2 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 30 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 30 h2 (* h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 15 h2 (* h4 h4) (* h5 h5) h6 j2) (* 3 h2 (* h4 h4) (* h5 h5) 
h6) (* 2 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10 h2 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 20 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 20 h2 h4 (* h5 h5 
h5) h6 (* j2 j2)) (* 10 h2 h4 (* h5 h5 h5) h6 j2) (* 2 h2 h4 (* h5 h5 h5) h6) 
(* 3 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 30 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 h2 h4 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 15 h2 h4 (* h5 h5) (* h6 h6) j2) (* 3 h2 h4 
(* h5 h5) (* h6 h6)) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h2 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 10 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5 h5) (* h6 h6) 
j2) (* h2 (* h5 h5 h5) (* h6 h6)) (* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 5 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5) 
(* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 6 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 15 (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 20 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2)) (* 15 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 6 (* h3 h3 h3) (* h4 h4) h5 
j2) (* (* h3 h3 h3) (* h4 h4) h5) (* (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 6 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 15 (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 20 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 15 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 6 (* h3 h3 h3) h4 (* h5 h5) j2) (* (* h3
 h3 h3) h4 (* h5 h5)) (* 2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 12 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 30 (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2)) (* 40 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 30 (* h3 h3 h3) h4 h5 h6 
(* j2 j2)) (* 12 (* h3 h3 h3) h4 h5 h6 j2) (* 2 (* h3 h3 h3) h4 h5 h6) (* (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 15 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 20 (* h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2)) (* 15 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 6 (* 
h3 h3 h3) (* h5 h5) h6 j2) (* (* h3 h3 h3) (* h5 h5) h6) (* (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 15 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2)) (* 15 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 6 (* h3 h3 h3) h5 
(* h6 h6) j2) (* (* h3 h3 h3) h5 (* h6 h6)) (* (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 15 (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 20 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2
)) (* 15 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4) h5 j2)
 (* (* h3 h3) (* h4 h4 h4) h5) (* 2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 12 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 30 (* h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 40 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 30 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 12 (* h3 h3) (* h4 h4)
 (* h5 h5) j2) (* 2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 3 (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 18 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 45 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 60 (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2)) (* 45 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 18 (* h3 h3) (* h4 
h4) h5 h6 j2) (* 3 (* h3 h3) (* h4 h4) h5 h6) (* (* h3 h3) h4 (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 6 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 15 (* h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 20 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2)) (* 15 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 6 (* h3 h3) h4 (* h5 h5 h5) 
j2) (* (* h3 h3) h4 (* h5 h5 h5)) (* 4 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 24 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60 (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 80 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 
60 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 24 (* h3 h3) h4 (* h5 h5) h6 j2) (* 4
 (* h3 h3) h4 (* h5 h5) h6) (* 3 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 18 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45 (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 60 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 45 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 18 (* h3 h3) h4 h5 (* h6 h6) j2) (* 3 (* h3
 h3) h4 h5 (* h6 h6)) (* (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 20 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 6 (* h3 h3) (* h5 h5 h5) h6 j2) (* (* h3 h3) (* h5
 h5 h5) h6) (* 2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 40 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 2 (* h3 h3) (* h5 h5) (* h6 h6)) (* (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 6 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
15 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h3 h3) h5 (* h6 h6 h6) j2) (* 
(* h3 h3) h5 (* h6 h6 h6)) (* h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 6 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 15 h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 20 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 15 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6 h3 (* h4 h4 h4) (* h5 h5) j2) (* h3 (* h4 h4
 h4) (* h5 h5)) (* h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 15 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2)) (* 20 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 15 h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2)) (* 6 h3 (* h4 h4) (* h5 h5 h5) j2) (* h3 (* h4 h4) (* h5 h5 h5
)) (* 3 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 45 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 60 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 45 h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 18 h3 (* h4 h4) (* h5 h5) h6 j2) (* 3 h3 (* h4 h4) (* h5 h5) h6) 
(* 2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 30 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 40 h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 30 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 12 h3 h4 
(* h5 h5 h5) h6 j2) (* 2 h3 h4 (* h5 h5 h5) h6) (* 3 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 18 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45
 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 60 h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 45 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 18 h3 h4 (* h5 h5) (* 
h6 h6) j2) (* 3 h3 h4 (* h5 h5) (* h6 h6)) (* h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 6 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h3 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 15 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 h3 (* h5 h5 h5) (* h6 h6) j2) 
(* h3 (* h5 h5 h5) (* h6 h6)) (* h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 6 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h3 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 20 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 15 h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 h3 (* h5 h5) (* h6 h6 h6) j2) (* h3 (* h5 h5
) (* h6 h6 h6))) 0)))
(check-sat)
(exit)
