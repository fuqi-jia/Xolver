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
(set-info :status unsat)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_9 (* skoX 5)) (?v_8 (* skoX 10)) (?v_6 (* skoX (- 5))) (?v_0 (* skoX (- 20))) (?v_2 (* skoX (- 30)))) (let ((?v_1 (+ (- 1260) (* skoX (+ 360 ?v_2)))) (?v_4 (+ 120 ?v_0)) (?v_7 (* skoY (- 5))) (?v_3 (* skoX (- 10))) (?v_5 (* skoY (- 10))) (?v_10 (+ (+ 2 (* skoX (- 1))) (* skoY (- 1))))) (and (<= (* skoZ (+ (+ (+ (- 15120) (* skoX (+ 6720 (* skoX (+ (- 1260) (* skoX (+ 120 ?v_6))))))) (* skoY (+ (+ 6720 (* skoX (+ (- 2520) (* skoX (+ 360 ?v_0))))) (* skoY (+ ?v_1 (* skoY (+ ?v_4 ?v_7))))))) (* skoZ (+ (+ (+ 3360 (* skoX (+ (- 1260) (* skoX (+ 180 ?v_3))))) (* skoY (+ ?v_1 (* skoY (+ (+ 180 ?v_2) ?v_5))))) (* skoZ (+ (+ (+ (- 420) (* skoX (+ 120 ?v_3))) (* skoY (+ ?v_4 ?v_5))) (* skoZ (+ (+ (+ 30 ?v_6) ?v_7) (* skoZ (- 1)))))))))) (+ (+ (- 30240) (* skoX (+ 15120 (* skoX (+ (- 3360) (* skoX (+ 420 (* skoX (+ (- 30) skoX))))))))) (* skoY (+ (+ 15120 (* skoX (+ (- 6720) (* skoX (+ 1260 (* skoX (+ (- 120) ?v_9))))))) (* skoY (+ (+ (- 3360) (* skoX (+ 1260 (* skoX (+ (- 180) ?v_8))))) (* skoY (+ (+ 420 (* skoX (+ (- 120) ?v_8))) (* skoY (+ (+ (- 30) ?v_9) skoY)))))))))) (and (<= 0 skoX) (and (<= 0 skoY) (and (<= 0 skoZ) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= skoZ ?v_10) (<= ?v_10 skoZ))))))))))))
(check-sat)
(exit)
