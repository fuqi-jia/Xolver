; IntBoundProp target (XOLVER_NIA_INT_BOUND_PROP): abstracting x*x to a free integer
; X gives X=2y with X bounded to [1,1], so 2y=1 — infeasible. The bound × equality
; interaction is invisible to the equalities-only modular reasoner; integer interval
; contraction empties y's domain ([INTBOUND] eqs=1 seeds=2 -> UNSAT). z3-confirmed.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x x) (* 2 y)))
(assert (>= (* x x) 1))
(assert (<= (* x x) 1))
(check-sat)
