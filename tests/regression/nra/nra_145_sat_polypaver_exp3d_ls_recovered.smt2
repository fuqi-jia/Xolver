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
(assert (let ((?v_11 (* skoX 6)) (?v_10 (* skoX 15)) (?v_8 (* skoX (- 6))) (?v_1 (* skoX (- 30))) (?v_0 (* skoX (- 60)))) (let ((?v_2 (+ 1152 (* skoX (+ (- 1008) (* skoX (+ 360 ?v_0)))))) (?v_3 (+ (- 336) (* skoX (+ 240 ?v_0)))) (?v_6 (+ 60 ?v_1)) (?v_9 (* skoY (- 6))) (?v_5 (* skoX (- 15))) (?v_4 (+ 120 ?v_0)) (?v_7 (* skoY (- 15)))) (and (<= (* skoZ (+ (+ (+ 2304 (* skoX (+ (- 2304) (* skoX (+ 1152 (* skoX (+ (- 336) (* skoX (+ 60 ?v_8))))))))) (* skoY (+ (+ (- 2304) (* skoX (+ 2304 (* skoX (+ (- 1008) (* skoX (+ 240 ?v_1))))))) (* skoY (+ ?v_2 (* skoY (+ ?v_3 (* skoY (+ ?v_6 ?v_9))))))))) (* skoZ (+ (+ (+ (- 1152) (* skoX (+ 1152 (* skoX (+ (- 504) (* skoX (+ 120 ?v_5))))))) (* skoY (+ ?v_2 (* skoY (+ (+ (- 504) (* skoX (+ 360 (* skoX (- 90))))) (* skoY (+ ?v_4 ?v_7))))))) (* skoZ (+ (+ (+ 384 (* skoX (+ (- 336) (* skoX (+ 120 (* skoX (- 20))))))) (* skoY (+ ?v_3 (* skoY (+ ?v_4 (* skoY (- 20))))))) (* skoZ (+ (+ (+ (- 84) (* skoX (+ 60 ?v_5))) (* skoY (+ ?v_6 ?v_7))) (* skoZ (+ (+ (+ 12 ?v_8) ?v_9) (* skoZ (- 1)))))))))))) (+ (+ 2304 (* skoX (+ (- 2304) (* skoX (+ 1152 (* skoX (+ (- 384) (* skoX (+ 84 (* skoX (+ (- 12) skoX))))))))))) (* skoY (+ (+ (- 2304) (* skoX (+ 2304 (* skoX (+ (- 1152) (* skoX (+ 336 (* skoX (+ (- 60) ?v_11))))))))) (* skoY (+ (+ 1152 (* skoX (+ (- 1152) (* skoX (+ 504 (* skoX (+ (- 120) ?v_10))))))) (* skoY (+ (+ (- 384) (* skoX (+ 336 (* skoX (+ (- 120) (* skoX 20)))))) (* skoY (+ (+ 84 (* skoX (+ (- 60) ?v_10))) (* skoY (+ (+ (- 12) ?v_11) skoY)))))))))))) (and (<= skoZ (+ (* skoX (- 1)) (* skoY (- 1)))) (and (<= skoZ 1) (and (<= skoY 1) (and (<= skoX 1) (and (<= 0 skoZ) (and (<= 0 skoY) (<= 0 skoX)))))))))))
(check-sat)
(exit)
