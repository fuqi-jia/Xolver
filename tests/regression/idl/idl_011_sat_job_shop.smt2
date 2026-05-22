; Job-shop scheduling: 3 jobs, 3 machines, each pair has precedence.
(set-logic QF_IDL)
(set-info :status sat)
(declare-const j1m1 Int) (declare-const j1m2 Int) (declare-const j1m3 Int)
(declare-const j2m1 Int) (declare-const j2m2 Int) (declare-const j2m3 Int)
(declare-const j3m1 Int) (declare-const j3m2 Int) (declare-const j3m3 Int)
; Each job: m1 → m2 → m3 with duration 2
(assert (>= (- j1m2 j1m1) 2))
(assert (>= (- j1m3 j1m2) 2))
(assert (>= (- j2m2 j2m1) 2))
(assert (>= (- j2m3 j2m2) 2))
(assert (>= (- j3m2 j3m1) 2))
(assert (>= (- j3m3 j3m2) 2))
; Earliest start
(assert (>= j1m1 0)) (assert (>= j2m1 0)) (assert (>= j3m1 0))
; Total time ≤ 30
(assert (<= j1m3 30)) (assert (<= j2m3 30)) (assert (<= j3m3 30))
(check-sat)
