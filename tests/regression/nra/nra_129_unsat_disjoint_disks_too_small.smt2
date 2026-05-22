; 2 disjoint radius=1/2 disks in unit square — impossible.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x1 Real) (declare-const y1 Real)
(declare-const x2 Real) (declare-const y2 Real)
; Centers must be in [1/2, 1/2] = single point.
(assert (>= x1 (/ 1 2))) (assert (<= x1 (/ 1 2)))
(assert (>= y1 (/ 1 2))) (assert (<= y1 (/ 1 2)))
(assert (>= x2 (/ 1 2))) (assert (<= x2 (/ 1 2)))
(assert (>= y2 (/ 1 2))) (assert (<= y2 (/ 1 2)))
; Disjoint ⇒ d² ≥ 1
(assert (>= (+ (* (- x1 x2) (- x1 x2)) (* (- y1 y2) (- y1 y2))) 1))
(check-sat)
