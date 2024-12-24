Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT2_REV_term_abbrevs.
Require Import REAL_POW_LT2_REV_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308562 (n : nat) : term0 n.
Proof. exact (@lem1651996 n). Qed.
Lemma lem2308563 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308564 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308563 n) (@lem2308562 n)). Qed.
Lemma lem2308565 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308564 n (real_of_int x)). Qed.
Lemma lem2308566 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308567 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308566 n x) (@lem2308565 n x)). Qed.
Lemma lem2308568 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308567 n x (real_of_int y)). Qed.
Lemma lem2308569 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308570 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308569 n x y) (@lem2308568 n x y)). Qed.
Lemma lem2308572 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308573 : term7 = term8.
Proof. exact (@lem2308572 (NUMERAL 0)). Qed.
Lemma lem2308574 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308575 : term9 = term10.
Proof. exact (MK_COMB (@lem2308574) (@lem2308573)). Qed.
Lemma lem2308576 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2308577 (y : int) : (term11 y) = (term12 y).
Proof. exact (MK_COMB (@lem2308575) (@lem2308576 y)). Qed.
Lemma lem2308579 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308580 (y : int) : (term12 y) = (term14 y).
Proof. exact (@lem2308579 term15 y). Qed.
Lemma lem2308581 (y : int) : (term11 y) = (term14 y).
Proof. exact (TRANS (@lem2308577 y) (@lem2308580 y)). Qed.
Lemma lem2308582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308583 (y : int) : (term16 y) = (term17 y).
Proof. exact (MK_COMB (@lem2308582) (@lem2308581 y)). Qed.
Lemma lem2308585 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308586 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308587 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2308586) (@lem2308585 x n)). Qed.
Lemma lem2308589 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308590 (y : int) (n : nat) : (term18 y n) = (term19 y n).
Proof. exact (@lem2308589 y n). Qed.
Lemma lem2308591 (x : int) (y : int) (n : nat) : (term22 x y n) = (term23 x y n).
Proof. exact (MK_COMB (@lem2308587 x n) (@lem2308590 y n)). Qed.
Lemma lem2308593 (x : int) (y : int) : (term24 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308594 (x : int) (y : int) (n : nat) : (term23 x y n) = (term25 x y n).
Proof. exact (@lem2308593 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308595 (x : int) (y : int) (n : nat) : (term22 x y n) = (term25 x y n).
Proof. exact (TRANS (@lem2308591 x y n) (@lem2308594 x y n)). Qed.
Lemma lem2308596 (x : int) (y : int) (n : nat) : (term26 x y n) = (term27 x y n).
Proof. exact (MK_COMB (@lem2308583 y) (@lem2308595 x y n)). Qed.
Lemma lem2308597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308598 (x : int) (y : int) (n : nat) : (term28 x y n) = (term29 x y n).
Proof. exact (MK_COMB (@lem2308597) (@lem2308596 x y n)). Qed.
Lemma lem2308600 (x : int) (y : int) : (term24 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308601 (n : nat) (x : int) (y : int) : (term5 n x y) = (term30 n x y).
Proof. exact (MK_COMB (@lem2308598 x y n) (@lem2308600 x y)). Qed.
Lemma lem2308602 (n : nat) (x : int) (y : int) : term30 n x y.
Proof. exact (EQ_MP (@lem2308601 n x y) (@lem2308570 n x y)). Qed.
Lemma lem2308603 (n : nat) (x : int) : term31 n x.
Proof. exact (fun y : int => @lem2308602 n x y). Qed.
Lemma lem2308604 (n : nat) : term32 n.
Proof. exact (fun x : int => @lem2308603 n x). Qed.
Lemma lem2308605 : term33.
Proof. exact (fun n : nat => @lem2308604 n). Qed.
