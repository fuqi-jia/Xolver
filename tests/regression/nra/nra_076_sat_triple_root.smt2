; (x-2)^3 = 0 has triple root x=2. Stresses Squarefree engine: f/gcd(f,f') = x-2.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- x 2) (* (- x 2) (- x 2))) 0))
(check-sat)
