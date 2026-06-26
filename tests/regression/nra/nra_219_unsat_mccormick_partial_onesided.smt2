; McCormick partial-bounds target (XOLVER_NRA_MCCORMICK_PARTIAL): x and y have only
; LOWER bounds (x>=2, y>=3), so the classic 4-bound McCormick relaxation bails. The
; partial lower-corner cut t >= lx*y + ly*x - lx*ly = 2y + 3x - 6 needs only those two
; lower bounds and gives x*y >= 6, contradicting x*y <= 5. z3-confirmed unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 2))
(assert (>= y 3))
(assert (<= (* x y) 5))
(check-sat)
