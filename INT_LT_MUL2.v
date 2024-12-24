Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_MUL2_term_abbrevs.
Require Import REAL_LT_MUL2_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2304394 (w : int) : term0 w.
Proof. exact (@lem1630835 (real_of_int w)). Qed.
Lemma lem2304395 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2304396 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2304395 w) (@lem2304394 w)). Qed.
Lemma lem2304397 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2304396 w (real_of_int x)). Qed.
Lemma lem2304398 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2304399 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2304398 w x) (@lem2304397 w x)). Qed.
Lemma lem2304400 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2304399 w x (real_of_int y)). Qed.
Lemma lem2304401 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2304402 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2304401 w y x) (@lem2304400 w x y)). Qed.
Lemma lem2304403 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2304402 w y x (real_of_int z)). Qed.
Lemma lem2304404 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2304405 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2304404 w y x z) (@lem2304403 w y x z)). Qed.
Lemma lem2304407 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304408 : term9 = term10.
Proof. exact (@lem2304407 (NUMERAL 0)). Qed.
Lemma lem2304409 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2304410 : term11 = term12.
Proof. exact (MK_COMB (@lem2304409) (@lem2304408)). Qed.
Lemma lem2304411 (w : int) : (real_of_int w) = (real_of_int w).
Proof. exact (eq_refl (real_of_int w)). Qed.
Lemma lem2304412 (w : int) : (term13 w) = (term14 w).
Proof. exact (MK_COMB (@lem2304410) (@lem2304411 w)). Qed.
Lemma lem2304414 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2304415 (w : int) : (term14 w) = (term16 w).
Proof. exact (@lem2304414 term17 w). Qed.
Lemma lem2304416 (w : int) : (term13 w) = (term16 w).
Proof. exact (TRANS (@lem2304412 w) (@lem2304415 w)). Qed.
Lemma lem2304417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304418 (w : int) : (term18 w) = (term19 w).
Proof. exact (MK_COMB (@lem2304417) (@lem2304416 w)). Qed.
Lemma lem2304420 (x : int) (y : int) : (term20 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304421 (w : int) (x : int) : (term20 w x) = (int_lt w x).
Proof. exact (@lem2304420 w x). Qed.
Lemma lem2304422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304423 (w : int) (x : int) : (term21 w x) = (term22 w x).
Proof. exact (MK_COMB (@lem2304422) (@lem2304421 w x)). Qed.
Lemma lem2304425 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304426 : term9 = term10.
Proof. exact (@lem2304425 (NUMERAL 0)). Qed.
Lemma lem2304427 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2304428 : term11 = term12.
Proof. exact (MK_COMB (@lem2304427) (@lem2304426)). Qed.
Lemma lem2304429 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304430 (y : int) : (term13 y) = (term14 y).
Proof. exact (MK_COMB (@lem2304428) (@lem2304429 y)). Qed.
Lemma lem2304432 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2304433 (y : int) : (term14 y) = (term16 y).
Proof. exact (@lem2304432 term17 y). Qed.
Lemma lem2304434 (y : int) : (term13 y) = (term16 y).
Proof. exact (TRANS (@lem2304430 y) (@lem2304433 y)). Qed.
Lemma lem2304435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304436 (y : int) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem2304435) (@lem2304434 y)). Qed.
Lemma lem2304438 (x : int) (y : int) : (term20 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304439 (y : int) (z : int) : (term20 y z) = (int_lt y z).
Proof. exact (@lem2304438 y z). Qed.
Lemma lem2304440 (y : int) (z : int) : (term23 y z) = (term24 y z).
Proof. exact (MK_COMB (@lem2304436 y) (@lem2304439 y z)). Qed.
Lemma lem2304441 (w : int) (x : int) (y : int) (z : int) : (term25 w x y z) = (term26 w x y z).
Proof. exact (MK_COMB (@lem2304423 w x) (@lem2304440 y z)). Qed.
Lemma lem2304442 (w : int) (x : int) (y : int) (z : int) : (term27 w x y z) = (term28 w x y z).
Proof. exact (MK_COMB (@lem2304418 w) (@lem2304441 w x y z)). Qed.
Lemma lem2304443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304444 (w : int) (x : int) (y : int) (z : int) : (term29 w x y z) = (term30 w x y z).
Proof. exact (MK_COMB (@lem2304443) (@lem2304442 w x y z)). Qed.
Lemma lem2304446 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304447 (w : int) (y : int) : (term31 w y) = (term32 w y).
Proof. exact (@lem2304446 w y). Qed.
Lemma lem2304448 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304449 (w : int) (y : int) : (term33 w y) = (term34 w y).
Proof. exact (MK_COMB (@lem2304448) (@lem2304447 w y)). Qed.
Lemma lem2304451 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304452 (x : int) (z : int) : (term31 x z) = (term32 x z).
Proof. exact (@lem2304451 x z). Qed.
Lemma lem2304453 (w : int) (y : int) (x : int) (z : int) : (term35 w y x z) = (term36 w y x z).
Proof. exact (MK_COMB (@lem2304449 w y) (@lem2304452 x z)). Qed.
Lemma lem2304455 (x : int) (y : int) : (term20 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304456 (w : int) (y : int) (x : int) (z : int) : (term36 w y x z) = (term37 w y x z).
Proof. exact (@lem2304455 (int_mul w y) (int_mul x z)). Qed.
Lemma lem2304457 (w : int) (y : int) (x : int) (z : int) : (term35 w y x z) = (term37 w y x z).
Proof. exact (TRANS (@lem2304453 w y x z) (@lem2304456 w y x z)). Qed.
Lemma lem2304458 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term38 w y x z).
Proof. exact (MK_COMB (@lem2304444 w x y z) (@lem2304457 w y x z)). Qed.
Lemma lem2304459 (w : int) (y : int) (x : int) (z : int) : term38 w y x z.
Proof. exact (EQ_MP (@lem2304458 w y x z) (@lem2304405 w y x z)). Qed.
Lemma lem2304460 (w : int) (y : int) (x : int) : term39 w y x.
Proof. exact (fun z : int => @lem2304459 w y x z). Qed.
Lemma lem2304461 (w : int) (x : int) : term40 w x.
Proof. exact (fun y : int => @lem2304460 w y x). Qed.
Lemma lem2304462 (w : int) : term41 w.
Proof. exact (fun x : int => @lem2304461 w x). Qed.
Lemma lem2304463 : term42.
Proof. exact (fun w : int => @lem2304462 w). Qed.
