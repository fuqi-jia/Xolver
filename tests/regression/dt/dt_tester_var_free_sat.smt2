; Tester on a FREE variable: (_ is cons) x is satisfiable (pick x = cons(...)).
; Guards the false-UNSAT direction: once testers register, the tester-consistency
; check must compare the tester's TARGET constructor (cons), not the tester name
; (is-cons), against a determined class constructor. Comparing the full tester
; name never matches and would spuriously refute a satisfiable tester.
(set-info :status sat)
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)) (((succ (pred nat)) (zero)) ((cons (car nat) (cdr list)) (null))))
(declare-fun x () list)
(assert ((_ is cons) x))
(check-sat)
