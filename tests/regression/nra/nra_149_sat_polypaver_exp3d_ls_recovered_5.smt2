(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (let ((?v_0 (* skoX (/ (- 81) 4))) (?v_1 (* skoX (/ 27 8))) (?v_2 (* skoY (/ 27 8))) (?v_3 (* skoX (/ (- 81) 2))) (?v_4 (+ (+ 2 (* skoX (- 1))) (* skoY (- 1))))) (and (not (<= (* skoZ (+ (+ (+ 180 (* skoX (+ (- 153) (* skoX (+ (/ (- 45) 2) (* skoX (/ (- 27) 4))))))) (* skoY (+ (+ (- 153) (* skoX (+ (- 45) ?v_0))) (* skoY (+ (+ (/ (- 45) 2) ?v_0) (* skoY (/ (- 27) 4))))))) (* skoZ (+ (+ (+ (- 174) (* skoX (+ (- 18) (* skoX (+ (/ (- 39) 4) (* skoX (/ 9 8))))))) (* skoY (+ (+ (- 18) (* skoX (+ (/ (- 39) 2) ?v_1))) (* skoY (+ (+ (/ (- 39) 4) ?v_1) (* skoY (/ 9 8))))))) (* skoZ (+ (+ (+ 18 (* skoX (+ (/ 3 4) ?v_1))) (* skoY (+ (+ (/ 3 4) (* skoX (/ 27 4))) ?v_2))) (* skoZ (+ (+ (+ (/ 15 4) ?v_1) ?v_2) (* skoZ (/ 9 8)))))))))) (+ (+ (- 1260) (* skoX (+ (- 810) (* skoX (+ (- 126) (* skoX (/ (- 27) 2))))))) (* skoY (+ (+ (- 810) (* skoX (+ (- 252) ?v_3))) (* skoY (+ (+ (- 126) ?v_3) (* skoY (/ (- 27) 2))))))))) (and (<= 0 skoX) (and (<= 0 skoY) (and (<= 0 skoZ) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= skoZ ?v_4) (<= ?v_4 skoZ)))))))))))
(check-sat)
(exit)
