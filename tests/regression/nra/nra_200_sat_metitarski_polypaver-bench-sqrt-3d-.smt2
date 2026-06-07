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
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_4 (<= skoY 1)) (?v_2 (not (<= skoZ 1))) (?v_3 (not (<= skoX 1)))) (let ((?v_5 (or (not ?v_4) ?v_2)) (?v_0 (* skoX (/ 1 2))) (?v_1 (+ (/ (- 1) 4) (* skoX (/ (- 1) 4)))) (?v_6 (* skoX (/ 1 4))) (?v_7 (* skoX (/ (- 5) 4)))) (and ?v_4 (and (or (not (<= (* skoZ (* skoY (+ (* skoX (+ (/ (- 7) 2) ?v_0)) (* skoY (* skoX (+ (/ 1 2) ?v_0)))))) (+ ?v_1 (* skoY ?v_1)))) ?v_2) (and (or ?v_3 ?v_2) (and (<= 1 skoX) (and (<= 1 skoY) (and (<= 1 skoZ) (and (<= skoX 2) (and (<= skoY 2) (and (<= skoZ 2) (and (or ?v_3 ?v_5) (and ?v_5 (or (not (<= (* skoZ (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 15) 4) ?v_6))) (* skoY (* skoX (* skoX (+ (/ 1 4) ?v_6)))))))) (* skoY (+ (* skoX (+ (/ 11 4) ?v_7)) (* skoY (* skoX (+ (/ (- 5) 4) ?v_7))))))) ?v_2)))))))))))))))
(check-sat)
(exit)
