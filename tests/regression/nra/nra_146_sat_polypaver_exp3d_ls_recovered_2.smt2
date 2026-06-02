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
(assert (let ((?v_8 (* skoX (/ (- 3) 4))) (?v_1 (* skoX (/ (- 15) 4))) (?v_0 (* skoX (/ (- 15) 2)))) (let ((?v_2 (+ 144 (* skoX (+ (- 126) (* skoX (+ 45 ?v_0)))))) (?v_3 (+ (- 42) (* skoX (+ 30 ?v_0)))) (?v_6 (+ (/ 15 2) ?v_1)) (?v_9 (* skoY (/ (- 3) 4))) (?v_5 (* skoX (/ (- 15) 8))) (?v_4 (+ 15 ?v_0)) (?v_7 (* skoY (/ (- 15) 8))) (?v_11 (* skoX (/ 3 4))) (?v_10 (* skoX (/ 15 8)))) (and (<= skoZ (+ (* skoX (- 1)) (* skoY (- 1)))) (and (not (<= (* skoZ (+ (+ (+ 288 (* skoX (+ (- 288) (* skoX (+ 144 (* skoX (+ (- 42) (* skoX (+ (/ 15 2) ?v_8))))))))) (* skoY (+ (+ (- 288) (* skoX (+ 288 (* skoX (+ (- 126) (* skoX (+ 30 ?v_1))))))) (* skoY (+ ?v_2 (* skoY (+ ?v_3 (* skoY (+ ?v_6 ?v_9))))))))) (* skoZ (+ (+ (+ (- 144) (* skoX (+ 144 (* skoX (+ (- 63) (* skoX (+ 15 ?v_5))))))) (* skoY (+ ?v_2 (* skoY (+ (+ (- 63) (* skoX (+ 45 (* skoX (/ (- 45) 4))))) (* skoY (+ ?v_4 ?v_7))))))) (* skoZ (+ (+ (+ 48 (* skoX (+ (- 42) (* skoX (+ 15 (* skoX (/ (- 5) 2))))))) (* skoY (+ ?v_3 (* skoY (+ ?v_4 (* skoY (/ (- 5) 2))))))) (* skoZ (+ (+ (+ (/ (- 21) 2) (* skoX (+ (/ 15 2) ?v_5))) (* skoY (+ ?v_6 ?v_7))) (* skoZ (+ (+ (+ (/ 3 2) ?v_8) ?v_9) (* skoZ (/ (- 1) 8)))))))))))) (+ (+ (- 2016) (* skoX (+ (- 288) (* skoX (+ 144 (* skoX (+ (- 48) (* skoX (+ (/ 21 2) (* skoX (+ (/ (- 3) 2) (* skoX (/ 1 8))))))))))))) (* skoY (+ (+ (- 288) (* skoX (+ 288 (* skoX (+ (- 144) (* skoX (+ 42 (* skoX (+ (/ (- 15) 2) ?v_11))))))))) (* skoY (+ (+ 144 (* skoX (+ (- 144) (* skoX (+ 63 (* skoX (+ (- 15) ?v_10))))))) (* skoY (+ (+ (- 48) (* skoX (+ 42 (* skoX (+ (- 15) (* skoX (/ 5 2))))))) (* skoY (+ (+ (/ 21 2) (* skoX (+ (/ (- 15) 2) ?v_10))) (* skoY (+ (+ (/ (- 3) 2) ?v_11) (* skoY (/ 1 8))))))))))))))) (and (<= skoZ 1) (and (<= skoY 1) (and (<= skoX 1) (and (<= 0 skoZ) (and (<= 0 skoY) (<= 0 skoX)))))))))))
(check-sat)
(exit)
