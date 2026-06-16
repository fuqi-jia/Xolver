; Small-prime-modular target behind a nonlinear monomial: abstracting x*x to a free
; integer X gives X+y=0 ∧ X-y=1 ⟹ 2X=1, infeasible mod 2. The linear-equality
; presolve (Smith-NF) cannot reach this because x*x is nonlinear; the modular stage's
; monomial abstraction does (XOLVER_NIA_SMALL_PRIME_MODULAR: [MODULAR] eqs=2 -> UNSAT).
; z3-confirmed unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* x x) y) 0))
(assert (= (- (* x x) y) 1))
(check-sat)
