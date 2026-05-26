; Row2 fall-through with distinct CONSTANT indices: 1!=2 so
; select(store(a,1,10),2)=select(a,2). Guards the const-index arith-decided atom.
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-const a (Array Int Int))
(assert (= (select a 2) 99))
(assert (not (= (select (store a 1 10) 2) 99)))
(check-sat)
