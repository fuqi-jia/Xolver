(set-logic QF_RDL)
(set-info :status sat)
; x - y <= 5 and y < x : satisfiable; exercises RDL model read-off.
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= (- x y) 5.0))
(assert (< (- y x) 0.0))
(check-sat)
