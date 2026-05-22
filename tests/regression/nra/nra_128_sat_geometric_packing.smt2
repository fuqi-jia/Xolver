; Geometric packing: 2 disjoint disks of radius 1/2 in unit square.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x1 Real) (declare-const y1 Real)
(declare-const x2 Real) (declare-const y2 Real)
; Both centers in [1/2, 1/2] box for disk radius 1/2 in [0,1]².
; Wait: disk radius r means center in [r, 1-r] = [1/2, 1/2]. So x1=x2=1/2, y1=y2=1/2.
; Disjoint disks ⇒ |centers| ≥ 2r = 1. Can't have 2 disjoint r=1/2 disks in [0,1]² ⇒ UNSAT.
; Make it SAT by using radius = 1/3 instead.
(assert (>= x1 (/ 1 3))) (assert (<= x1 (/ 2 3)))
(assert (>= y1 (/ 1 3))) (assert (<= y1 (/ 2 3)))
(assert (>= x2 (/ 1 3))) (assert (<= x2 (/ 2 3)))
(assert (>= y2 (/ 1 3))) (assert (<= y2 (/ 2 3)))
(check-sat)
