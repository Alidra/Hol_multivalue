Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LTE_ADD_term_abbrevs.
Require Import REAL_LTE_ADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303484 (x : int) : term0 x.
Proof. exact (@lem1380653 (real_of_int x)). Qed.
Lemma lem2303485 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303486 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303485 x) (@lem2303484 x)). Qed.
Lemma lem2303487 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303486 x (real_of_int y)). Qed.
Lemma lem2303488 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303489 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303488 x y) (@lem2303487 x y)). Qed.
Lemma lem2303491 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303492 : term5 = term6.
Proof. exact (@lem2303491 (NUMERAL 0)). Qed.
Lemma lem2303493 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303494 : term7 = term8.
Proof. exact (MK_COMB (@lem2303493) (@lem2303492)). Qed.
Lemma lem2303495 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2303496 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2303494) (@lem2303495 x)). Qed.
Lemma lem2303498 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303499 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2303498 term13 x). Qed.
Lemma lem2303500 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2303496 x) (@lem2303499 x)). Qed.
Lemma lem2303501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303502 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2303501) (@lem2303500 x)). Qed.
Lemma lem2303504 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303505 : term5 = term6.
Proof. exact (@lem2303504 (NUMERAL 0)). Qed.
Lemma lem2303506 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303507 : term16 = term17.
Proof. exact (MK_COMB (@lem2303506) (@lem2303505)). Qed.
Lemma lem2303508 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2303509 (y : int) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem2303507) (@lem2303508 y)). Qed.
Lemma lem2303511 (x : int) (y : int) : (term20 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303512 (y : int) : (term19 y) = (term21 y).
Proof. exact (@lem2303511 term13 y). Qed.
Lemma lem2303513 (y : int) : (term18 y) = (term21 y).
Proof. exact (TRANS (@lem2303509 y) (@lem2303512 y)). Qed.
Lemma lem2303514 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2303502 x) (@lem2303513 y)). Qed.
Lemma lem2303515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303516 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2303515) (@lem2303514 x y)). Qed.
Lemma lem2303518 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303519 : term5 = term6.
Proof. exact (@lem2303518 (NUMERAL 0)). Qed.
Lemma lem2303520 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303521 : term7 = term8.
Proof. exact (MK_COMB (@lem2303520) (@lem2303519)). Qed.
Lemma lem2303523 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303524 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem2303521) (@lem2303523 x y)). Qed.
Lemma lem2303526 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303527 (x : int) (y : int) : (term29 x y) = (term30 x y).
Proof. exact (@lem2303526 term13 (int_add x y)). Qed.
Lemma lem2303528 (x : int) (y : int) : (term28 x y) = (term30 x y).
Proof. exact (TRANS (@lem2303524 x y) (@lem2303527 x y)). Qed.
Lemma lem2303529 (x : int) (y : int) : (term3 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem2303516 x y) (@lem2303528 x y)). Qed.
Lemma lem2303530 (x : int) (y : int) : term31 x y.
Proof. exact (EQ_MP (@lem2303529 x y) (@lem2303489 x y)). Qed.
Lemma lem2303531 (x : int) : term32 x.
Proof. exact (fun y : int => @lem2303530 x y). Qed.
Lemma lem2303532 : term33.
Proof. exact (fun x : int => @lem2303531 x). Qed.
