(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
; Independent monomial columns admit x=0, x^2=2. That is not an original model.
(assert (= (* x x) 2))
(assert (= x 0))
(check-sat)
