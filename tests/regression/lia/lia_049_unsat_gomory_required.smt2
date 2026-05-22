; Gomory cut required: LP relaxation feasible but integer infeasible.
; 2x + 3y = 7, x ≥ 0, y ≥ 0 — solutions (2,1), (1,5/3 no). Add eq: solution unique.
; Force unsat: 2x + 3y = 7 ∧ 2x + 3y = 8 — clearly unsat (Simplex sufficient).
; For real Gomory: x + y ≤ 5, x + y ≥ 4, 2x + 4y = 9 — LP says 9/4 < y < 5/2, no int. UNSAT in LIA.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0)) (assert (>= y 0))
(assert (<= (+ x y) 5)) (assert (>= (+ x y) 4))
(assert (= (+ (* 2 x) (* 4 y)) 9))
(check-sat)
