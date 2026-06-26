; Small-prime-modular target: x+y=0 ∧ x-y=1 jointly force 2x=1, which is infeasible
; (no integer x). Each equation alone has coefficient-gcd 1, so the per-equation gcd
; test cannot see it — it is a SYSTEM-level obstruction, infeasible mod 2. z3-confirmed.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 0))
(assert (= (- x y) 1))
(check-sat)
