; Tester MATCHES its own applied constructor: (_ is cons) (cons (data (leaf zero))
; null) is true, so the assertion is satisfiable. Guards the same-constructor
; direction of the tester-consistency check (target ctor cons == class ctor cons
; must NOT conflict).
(set-info :status sat)
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (
  ((succ (pred nat)) (zero))
  ((cons (car tree) (cdr list)) (null))
  ((node (children list)) (leaf (data nat)))))
(assert ((_ is cons) (cons (leaf zero) null)))
(check-sat)
