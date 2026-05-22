; (x-a)² + (y-b)² < 0 is unsat (translated SOS).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ (* (- x 3) (- x 3)) (* (- y 5) (- y 5))) 0))
(check-sat)
