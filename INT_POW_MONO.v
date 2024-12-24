Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_MONO_term_abbrevs.
Require Import REAL_POW_MONO_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308643 (m : nat) : term0 m.
Proof. exact (@lem1637789 m). Qed.
Lemma lem2308644 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2308645 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2308644 m) (@lem2308643 m)). Qed.
Lemma lem2308646 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2308645 m n). Qed.
Lemma lem2308647 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2308648 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem2308647 m n) (@lem2308646 m n)). Qed.
Lemma lem2308649 (m : nat) (n : nat) (x : int) : term4 m n x.
Proof. exact (@lem2308648 m n (real_of_int x)). Qed.
Lemma lem2308650 (m : nat) (x : int) (n : nat) : (term4 m n x) = (term5 m x n).
Proof. exact (eq_refl (term4 m n x)). Qed.
Lemma lem2308651 (m : nat) (x : int) (n : nat) : term5 m x n.
Proof. exact (EQ_MP (@lem2308650 m x n) (@lem2308649 m n x)). Qed.
Lemma lem2308653 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308654 : term7 = term8.
Proof. exact (@lem2308653 term9). Qed.
Lemma lem2308655 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308656 : term10 = term11.
Proof. exact (MK_COMB (@lem2308655) (@lem2308654)). Qed.
Lemma lem2308657 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308658 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2308656) (@lem2308657 x)). Qed.
Lemma lem2308660 (x : int) (y : int) : (term14 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308661 (x : int) : (term13 x) = (term15 x).
Proof. exact (@lem2308660 term16 x). Qed.
Lemma lem2308662 (x : int) : (term12 x) = (term15 x).
Proof. exact (TRANS (@lem2308658 x) (@lem2308661 x)). Qed.
Lemma lem2308663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308664 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2308663) (@lem2308662 x)). Qed.
Lemma lem2308665 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem2308666 (x : int) (m : nat) (n : nat) : (term19 x m n) = (term20 x m n).
Proof. exact (MK_COMB (@lem2308664 x) (@lem2308665 m n)). Qed.
Lemma lem2308667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308668 (x : int) (m : nat) (n : nat) : (term21 x m n) = (term22 x m n).
Proof. exact (MK_COMB (@lem2308667) (@lem2308666 x m n)). Qed.
Lemma lem2308670 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308671 (x : int) (m : nat) : (term23 x m) = (term24 x m).
Proof. exact (@lem2308670 x m). Qed.
Lemma lem2308672 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308673 (x : int) (m : nat) : (term25 x m) = (term26 x m).
Proof. exact (MK_COMB (@lem2308672) (@lem2308671 x m)). Qed.
Lemma lem2308675 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308676 (m : nat) (x : int) (n : nat) : (term27 m x n) = (term28 m x n).
Proof. exact (MK_COMB (@lem2308673 x m) (@lem2308675 x n)). Qed.
Lemma lem2308678 (x : int) (y : int) : (term14 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308679 (m : nat) (x : int) (n : nat) : (term28 m x n) = (term29 m x n).
Proof. exact (@lem2308678 (int_pow x m) (int_pow x n)). Qed.
Lemma lem2308680 (m : nat) (x : int) (n : nat) : (term27 m x n) = (term29 m x n).
Proof. exact (TRANS (@lem2308676 m x n) (@lem2308679 m x n)). Qed.
Lemma lem2308681 (m : nat) (x : int) (n : nat) : (term5 m x n) = (term30 m x n).
Proof. exact (MK_COMB (@lem2308668 x m n) (@lem2308680 m x n)). Qed.
Lemma lem2308682 (m : nat) (x : int) (n : nat) : term30 m x n.
Proof. exact (EQ_MP (@lem2308681 m x n) (@lem2308651 m x n)). Qed.
Lemma lem2308683 (m : nat) (n : nat) : term31 m n.
Proof. exact (fun x : int => @lem2308682 m x n). Qed.
Lemma lem2308684 (m : nat) : term32 m.
Proof. exact (fun n : nat => @lem2308683 m n). Qed.
Lemma lem2308685 : term33.
Proof. exact (fun m : nat => @lem2308684 m). Qed.
