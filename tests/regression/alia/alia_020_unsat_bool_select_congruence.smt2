; Bool-valued array read is an EUF-owned predicate: equal indices -> equal reads.
; Regression for the combination bool-predicate routing fix (was false-SAT).
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun arr () (Array Int Bool))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (select arr i))
(assert (not (select arr j)))
(assert (= i j))
(check-sat)
