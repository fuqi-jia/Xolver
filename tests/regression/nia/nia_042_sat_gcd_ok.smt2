; 3x + 6y = 9 has gcd(3,6)=3 | 9, sat (x=1,y=1 or x=3,y=0).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 3 x) (* 6 y)) 9))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
