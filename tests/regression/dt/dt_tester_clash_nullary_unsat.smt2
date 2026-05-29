; Tester on a DIFFERENT nullary constructor: (_ is cons) null. null is the `null`
; constructor of list, not cons, so is_cons(null) is definitionally false and the
; assertion is unsat. Regression for the QF_DT tester-on-constructor false-SAT
; class: before the parser/atomizer/DtReasoner fix, (_ is C) parsed as an opaque
; UF apply and the tester was never refuted -> false SAT.
(set-info :status unsat)
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)) (((succ (pred nat)) (zero)) ((cons (car nat) (cdr list)) (null))))
(assert ((_ is cons) null))
(check-sat)
