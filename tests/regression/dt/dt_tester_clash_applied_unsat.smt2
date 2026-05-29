; Tester on a DIFFERENT applied constructor over mutually-recursive datatypes:
; (_ is node) (leaf (data x)). leaf and node are both `tree` constructors;
; is_node(leaf ...) is definitionally false -> unsat. Exercises the 3-way mutual
; declare-datatypes (nat/list/tree) form from the SMT-COMP QF_DT benchmark, where
; the tester clash on an applied constructor was left unrefuted (false SAT).
(set-info :status unsat)
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (
  ((succ (pred nat)) (zero))
  ((cons (car tree) (cdr list)) (null))
  ((node (children list)) (leaf (data nat)))))
(declare-fun x () nat)
(assert ((_ is node) (leaf (data x))))
(check-sat)
