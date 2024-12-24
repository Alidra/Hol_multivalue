Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_EQ_INEQ_term_abbrevs.
Require Import REAL_SGN_EQ_INEQ_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309450 (x : int) : term0 x.
Proof. exact (@lem1821194 (real_of_int x)). Qed.
Lemma lem2309451 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309452 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309451 x) (@lem2309450 x)). Qed.
Lemma lem2309453 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2309452 x (real_of_int y)). Qed.
Lemma lem2309454 (x : int) (y : int) : (term2 x y) = (((term3 x) = (term3 y)) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2309455 (x : int) (y : int) : ((term3 x) = (term3 y)) = (term4 x y).
Proof. exact (EQ_MP (@lem2309454 x y) (@lem2309453 x y)). Qed.
Lemma lem2309457 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309458 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309459 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2309458) (@lem2309457 x)). Qed.
Lemma lem2309461 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309462 (y : int) : (term3 y) = (term5 y).
Proof. exact (@lem2309461 y). Qed.
Lemma lem2309463 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term5 x) = (term5 y)).
Proof. exact (MK_COMB (@lem2309459 x) (@lem2309462 y)). Qed.
Lemma lem2309465 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309466 (x : int) (y : int) : ((term5 x) = (term5 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (@lem2309465 (int_sgn x) (int_sgn y)). Qed.
Lemma lem2309467 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (TRANS (@lem2309463 x y) (@lem2309466 x y)). Qed.
Lemma lem2309468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309469 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2309468) (@lem2309467 x y)). Qed.
Lemma lem2309471 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2309473 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2309472) (@lem2309471 x y)). Qed.
Lemma lem2309475 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2309476 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2309477 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2309476) (@lem2309475 x y)). Qed.
Lemma lem2309479 (x : int) : (term16 x) = (term17 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309480 (x : int) (y : int) : (term15 x y) = (term18 x y).
Proof. exact (@lem2309479 (int_sub x y)). Qed.
Lemma lem2309481 (x : int) (y : int) : (term14 x y) = (term18 x y).
Proof. exact (TRANS (@lem2309477 x y) (@lem2309480 x y)). Qed.
Lemma lem2309482 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2309483 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2309482) (@lem2309481 x y)). Qed.
Lemma lem2309485 (x : int) : (term16 x) = (term17 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309486 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2309487 (x : int) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem2309486) (@lem2309485 x)). Qed.
Lemma lem2309489 (x : int) : (term16 x) = (term17 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309490 (y : int) : (term16 y) = (term17 y).
Proof. exact (@lem2309489 y). Qed.
Lemma lem2309491 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem2309487 x) (@lem2309490 y)). Qed.
Lemma lem2309493 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2309494 (x : int) (y : int) : (term24 x y) = (term27 x y).
Proof. exact (@lem2309493 (int_abs x) (int_abs y)). Qed.
Lemma lem2309495 (x : int) (y : int) : (term23 x y) = (term27 x y).
Proof. exact (TRANS (@lem2309491 x y) (@lem2309494 x y)). Qed.
Lemma lem2309496 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem2309483 x y) (@lem2309495 x y)). Qed.
Lemma lem2309498 (x : int) (y : int) : (term30 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309499 (x : int) (y : int) : (term29 x y) = (term31 x y).
Proof. exact (@lem2309498 (term32 x y) (term33 x y)). Qed.
Lemma lem2309500 (x : int) (y : int) : (term28 x y) = (term31 x y).
Proof. exact (TRANS (@lem2309496 x y) (@lem2309499 x y)). Qed.
Lemma lem2309501 (x : int) (y : int) : (term4 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem2309473 x y) (@lem2309500 x y)). Qed.
Lemma lem2309502 (x : int) (y : int) : (((term3 x) = (term3 y)) = (term4 x y)) = (((int_sgn x) = (int_sgn y)) = (term34 x y)).
Proof. exact (MK_COMB (@lem2309469 x y) (@lem2309501 x y)). Qed.
Lemma lem2309503 (x : int) (y : int) : ((int_sgn x) = (int_sgn y)) = (term34 x y).
Proof. exact (EQ_MP (@lem2309502 x y) (@lem2309455 x y)). Qed.
Lemma lem2309504 (x : int) : term35 x.
Proof. exact (fun y : int => @lem2309503 x y). Qed.
Lemma lem2309505 : term36.
Proof. exact (fun x : int => @lem2309504 x). Qed.
