; McCormick partial-bounds SAT control: same one-sided box (x>=2, y>=3) but x*y>=10 is
; satisfiable (x=2, y=5). Guards against the partial cut over-constraining — a wrong
; cut here would yield a false unsat. z3-confirmed sat.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 2))
(assert (>= y 3))
(assert (>= (* x y) 10))
(check-sat)
