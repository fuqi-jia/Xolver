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
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_0 (* skoX (/ 27 8))) (?v_1 (* skoY (/ 27 8))) (?v_2 (* skoX (/ (- 27) 8))) (?v_3 (+ (+ 2 (* skoX (- 1))) (* skoY (- 1))))) (and (not (<= (* skoZ (+ (+ (+ (/ 135 2) (* skoX (+ 21 ?v_0))) (* skoY (+ (+ 21 (* skoX (/ 27 4))) ?v_1))) (* skoZ (+ (+ (+ (/ 21 2) ?v_0) ?v_1) (* skoZ (/ 9 8)))))) (+ (+ (- 105) (* skoX (+ (/ (- 135) 2) (* skoX (+ (/ (- 21) 2) (* skoX (/ (- 9) 8))))))) (* skoY (+ (+ (/ (- 135) 2) (* skoX (+ (- 21) ?v_2))) (* skoY (+ (+ (/ (- 21) 2) ?v_2) (* skoY (/ (- 9) 8))))))))) (and (<= ?v_3 skoZ) (and (<= skoZ ?v_3) (and (<= skoZ 1) (and (<= skoY 1) (and (<= skoX 1) (and (<= 0 skoZ) (and (<= 0 skoY) (<= 0 skoX)))))))))))
(check-sat)
(exit)
