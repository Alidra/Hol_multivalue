Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT2_term_abbrevs.
Require Import REAL_POW_LT2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308450 (n : nat) : term0 n.
Proof. exact (@lem1638321 n). Qed.
Lemma lem2308451 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308452 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308451 n) (@lem2308450 n)). Qed.
Lemma lem2308453 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308452 n (real_of_int x)). Qed.
Lemma lem2308454 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308455 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308454 x n) (@lem2308453 n x)). Qed.
Lemma lem2308456 (x : int) (n : nat) (y : int) : term4 x n y.
Proof. exact (@lem2308455 x n (real_of_int y)). Qed.
Lemma lem2308457 (x : int) (y : int) (n : nat) : (term4 x n y) = (term5 x y n).
Proof. exact (eq_refl (term4 x n y)). Qed.
Lemma lem2308458 (x : int) (y : int) (n : nat) : term5 x y n.
Proof. exact (EQ_MP (@lem2308457 x y n) (@lem2308456 x n y)). Qed.
Lemma lem2308460 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308461 : term7 = term8.
Proof. exact (@lem2308460 (NUMERAL 0)). Qed.
Lemma lem2308462 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308463 : term9 = term10.
Proof. exact (MK_COMB (@lem2308462) (@lem2308461)). Qed.
Lemma lem2308464 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308465 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2308463) (@lem2308464 x)). Qed.
Lemma lem2308467 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308468 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2308467 term15 x). Qed.
Lemma lem2308469 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2308465 x) (@lem2308468 x)). Qed.
Lemma lem2308470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308471 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2308470) (@lem2308469 x)). Qed.
Lemma lem2308473 (x : int) (y : int) : (term18 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308474 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2308471 x) (@lem2308473 x y)). Qed.
Lemma lem2308475 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem2308476 (n : nat) (x : int) (y : int) : (term22 n x y) = (term23 n x y).
Proof. exact (MK_COMB (@lem2308475 n) (@lem2308474 x y)). Qed.
Lemma lem2308477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308478 (n : nat) (x : int) (y : int) : (term24 n x y) = (term25 n x y).
Proof. exact (MK_COMB (@lem2308477) (@lem2308476 n x y)). Qed.
Lemma lem2308480 (x : int) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308481 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308482 (x : int) (n : nat) : (term28 x n) = (term29 x n).
Proof. exact (MK_COMB (@lem2308481) (@lem2308480 x n)). Qed.
Lemma lem2308484 (x : int) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308485 (y : int) (n : nat) : (term26 y n) = (term27 y n).
Proof. exact (@lem2308484 y n). Qed.
Lemma lem2308486 (x : int) (y : int) (n : nat) : (term30 x y n) = (term31 x y n).
Proof. exact (MK_COMB (@lem2308482 x n) (@lem2308485 y n)). Qed.
Lemma lem2308488 (x : int) (y : int) : (term18 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308489 (x : int) (y : int) (n : nat) : (term31 x y n) = (term32 x y n).
Proof. exact (@lem2308488 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308490 (x : int) (y : int) (n : nat) : (term30 x y n) = (term32 x y n).
Proof. exact (TRANS (@lem2308486 x y n) (@lem2308489 x y n)). Qed.
Lemma lem2308491 (x : int) (y : int) (n : nat) : (term5 x y n) = (term33 x y n).
Proof. exact (MK_COMB (@lem2308478 n x y) (@lem2308490 x y n)). Qed.
Lemma lem2308492 (x : int) (y : int) (n : nat) : term33 x y n.
Proof. exact (EQ_MP (@lem2308491 x y n) (@lem2308458 x y n)). Qed.
Lemma lem2308493 (x : int) (n : nat) : term34 x n.
Proof. exact (fun y : int => @lem2308492 x y n). Qed.
Lemma lem2308494 (n : nat) : term35 n.
Proof. exact (fun x : int => @lem2308493 x n). Qed.
Lemma lem2308495 : term36.
Proof. exact (fun n : nat => @lem2308494 n). Qed.
