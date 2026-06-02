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
(assert (let ((?v_6 (* skoX (/ 45 8))) (?v_0 (* skoX (/ 45 2))) (?v_2 (* skoX (/ 135 4)))) (let ((?v_1 (+ (/ 2835 2) (* skoX (+ 315 ?v_2)))) (?v_4 (+ 105 ?v_0)) (?v_7 (* skoY (/ 45 8))) (?v_3 (* skoX (/ 45 4))) (?v_5 (* skoY (/ 45 4))) (?v_9 (* skoX (/ (- 45) 8))) (?v_8 (* skoX (/ (- 45) 4))) (?v_10 (+ (+ 2 (* skoX (- 1))) (* skoY (- 1))))) (and (not (<= (* skoZ (+ (+ (+ 17010 (* skoX (+ 5880 (* skoX (+ (/ 2835 2) (* skoX (+ 105 ?v_6))))))) (* skoY (+ (+ 5880 (* skoX (+ 2835 (* skoX (+ 315 ?v_0))))) (* skoY (+ ?v_1 (* skoY (+ ?v_4 ?v_7))))))) (* skoZ (+ (+ (+ 2940 (* skoX (+ (/ 2835 2) (* skoX (+ (/ 315 2) ?v_3))))) (* skoY (+ ?v_1 (* skoY (+ (+ (/ 315 2) ?v_2) ?v_5))))) (* skoZ (+ (+ (+ (/ 945 2) (* skoX (+ 105 ?v_3))) (* skoY (+ ?v_4 ?v_5))) (* skoZ (+ (+ (+ (/ 105 4) ?v_6) ?v_7) (* skoZ (/ 9 8)))))))))) (+ (+ (- 26460) (* skoX (+ (- 17010) (* skoX (+ (- 2940) (* skoX (+ (/ (- 945) 2) (* skoX (+ (/ (- 105) 4) (* skoX (/ (- 9) 8))))))))))) (* skoY (+ (+ (- 17010) (* skoX (+ (- 5880) (* skoX (+ (/ (- 2835) 2) (* skoX (+ (- 105) ?v_9))))))) (* skoY (+ (+ (- 2940) (* skoX (+ (/ (- 2835) 2) (* skoX (+ (/ (- 315) 2) ?v_8))))) (* skoY (+ (+ (/ (- 945) 2) (* skoX (+ (- 105) ?v_8))) (* skoY (+ (+ (/ (- 105) 4) ?v_9) (* skoY (/ (- 9) 8))))))))))))) (and (<= 0 skoX) (and (<= 0 skoY) (and (<= 0 skoZ) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= skoZ ?v_10) (<= ?v_10 skoZ))))))))))))
(check-sat)
(exit)
