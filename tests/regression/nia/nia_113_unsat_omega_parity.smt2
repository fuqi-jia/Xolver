; Omega-test target: the nonlinear monomial (x*x) abstracts to a free integer,
; leaving a linear-integer parity contradiction — x*x is forced both even (= 2z)
; and odd (= 2z+1 - 2y reduces to odd). The Omega stage (XOLVER_NIA_OMEGA) refutes
; the abstracted linear-integer system. UNSAT is independently z3-confirmed.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (+ (* x x) (* 2 y)) (+ (* 2 z) 1)))
(assert (= (* x x) (* 2 z)))
(check-sat)
