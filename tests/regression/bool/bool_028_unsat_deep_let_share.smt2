; let-bound shared subterm used 4 times — hash-consing should keep one node.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool) (declare-const q Bool)
(assert (let ((x (and p q))) (and x (not x))))
(check-sat)
