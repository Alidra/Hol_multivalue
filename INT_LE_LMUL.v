Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LMUL_term_abbrevs.
Require Import REAL_LE_LMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302487 (x : int) : term0 x.
Proof. exact (@lem1583207 (real_of_int x)). Qed.
Lemma lem2302488 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302489 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302488 x) (@lem2302487 x)). Qed.
Lemma lem2302490 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302489 x (real_of_int y)). Qed.
Lemma lem2302491 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302492 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2302491 y x) (@lem2302490 x y)). Qed.
Lemma lem2302493 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2302492 y x (real_of_int z)). Qed.
Lemma lem2302494 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2302495 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2302494 y x z) (@lem2302493 y x z)). Qed.
Lemma lem2302497 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302498 : term7 = term8.
Proof. exact (@lem2302497 (NUMERAL 0)). Qed.
Lemma lem2302499 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302500 : term9 = term10.
Proof. exact (MK_COMB (@lem2302499) (@lem2302498)). Qed.
Lemma lem2302501 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302502 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2302500) (@lem2302501 x)). Qed.
Lemma lem2302504 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302505 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2302504 term15 x). Qed.
Lemma lem2302506 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2302502 x) (@lem2302505 x)). Qed.
Lemma lem2302507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302508 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2302507) (@lem2302506 x)). Qed.
Lemma lem2302510 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302511 (y : int) (z : int) : (term13 y z) = (int_le y z).
Proof. exact (@lem2302510 y z). Qed.
Lemma lem2302512 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2302508 x) (@lem2302511 y z)). Qed.
Lemma lem2302513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302514 (x : int) (y : int) (z : int) : (term20 x y z) = (term21 x y z).
Proof. exact (MK_COMB (@lem2302513) (@lem2302512 x y z)). Qed.
Lemma lem2302516 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302517 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302518 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2302517) (@lem2302516 x y)). Qed.
Lemma lem2302520 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302521 (x : int) (z : int) : (term22 x z) = (term23 x z).
Proof. exact (@lem2302520 x z). Qed.
Lemma lem2302522 (y : int) (x : int) (z : int) : (term26 y x z) = (term27 y x z).
Proof. exact (MK_COMB (@lem2302518 x y) (@lem2302521 x z)). Qed.
Lemma lem2302524 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302525 (y : int) (x : int) (z : int) : (term27 y x z) = (term28 y x z).
Proof. exact (@lem2302524 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2302526 (y : int) (x : int) (z : int) : (term26 y x z) = (term28 y x z).
Proof. exact (TRANS (@lem2302522 y x z) (@lem2302525 y x z)). Qed.
Lemma lem2302527 (y : int) (x : int) (z : int) : (term5 y x z) = (term29 y x z).
Proof. exact (MK_COMB (@lem2302514 x y z) (@lem2302526 y x z)). Qed.
Lemma lem2302528 (y : int) (x : int) (z : int) : term29 y x z.
Proof. exact (EQ_MP (@lem2302527 y x z) (@lem2302495 y x z)). Qed.
Lemma lem2302529 (y : int) (x : int) : term30 y x.
Proof. exact (fun z : int => @lem2302528 y x z). Qed.
Lemma lem2302530 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2302529 y x). Qed.
Lemma lem2302531 : term32.
Proof. exact (fun x : int => @lem2302530 x). Qed.
