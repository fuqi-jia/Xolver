; Square cut: x² < 0 — should immediately produce nonneg cut.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< (* x x) 0))
(check-sat)
