(set-logic QF_IDL)
(set-info :status unsat)
; Regression guard for the boolpur sort bug (Averest QF_IDL false-SAT cluster):
; an iff between two BOOLEAN COMPOSITES — (and ...) and (or ...) — forces both
; operands through BoolSubtermPurifier into fresh `boolpur` variables. If those
; vars are created with NullSort, the Atomizer fails to recognize the iff as
; propositional and routes it to the IDL theory as an integer (dis)equality,
; losing the boolean link and yielding unsound SAT. With the bool sort
; correctly propagated to CoreIr, the iff stays propositional and the cycle
; x<=y, a, !b, iff => y<x is detected as UNSAT.
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (and a (<= (- x y) 0)) (or b (<= (- y x) (- 1)))))
(assert a)
(assert (not b))
(assert (<= (- x y) 0))
(check-sat)
