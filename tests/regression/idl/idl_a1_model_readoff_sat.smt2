(set-logic QF_IDL)
(set-info :status sat)
; 1 <= x - y <= 5 : satisfiable; exercises IDL Bellman-Ford model read-off.
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (- x y) 5))
(assert (<= (- y x) (- 1)))
(check-sat)
