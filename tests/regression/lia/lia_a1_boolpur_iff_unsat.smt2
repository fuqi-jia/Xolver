(set-logic QF_LIA)
(set-info :status unsat)
; LIA analog of the boolpur sort bug (Averest QF_LIA ParallelPrefixSum false-SAT).
; An iff between two boolean composites pushes both operands into fresh boolpur
; vars; if those carry NullSort the iff leaks into LIA as an integer equality
; and the formula is falsely SAT. Correctly kept propositional, it is UNSAT:
; a, !b, x<=y, and (a & x<=y) <=> (b | y<=x-1) force y<x against x<=y.
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (and a (<= x y)) (or b (<= y (- x 1)))))
(assert a)
(assert (not b))
(assert (<= x y))
(check-sat)
