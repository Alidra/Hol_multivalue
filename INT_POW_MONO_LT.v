Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_MONO_LT_term_abbrevs.
Require Import REAL_POW_MONO_LT_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2308686 (m : nat) : term0 m.
Proof. exact (@lem1640304 m). Qed.
Lemma lem2308687 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2308688 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2308687 m) (@lem2308686 m)). Qed.
Lemma lem2308689 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2308688 m n). Qed.
Lemma lem2308690 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2308691 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem2308690 m n) (@lem2308689 m n)). Qed.
Lemma lem2308692 (m : nat) (n : nat) (x : int) : term4 m n x.
Proof. exact (@lem2308691 m n (real_of_int x)). Qed.
Lemma lem2308693 (m : nat) (x : int) (n : nat) : (term4 m n x) = (term5 m x n).
Proof. exact (eq_refl (term4 m n x)). Qed.
Lemma lem2308694 (m : nat) (x : int) (n : nat) : term5 m x n.
Proof. exact (EQ_MP (@lem2308693 m x n) (@lem2308692 m n x)). Qed.
Lemma lem2308696 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308697 : term7 = term8.
Proof. exact (@lem2308696 term9). Qed.
Lemma lem2308698 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308699 : term10 = term11.
Proof. exact (MK_COMB (@lem2308698) (@lem2308697)). Qed.
Lemma lem2308700 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308701 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2308699) (@lem2308700 x)). Qed.
Lemma lem2308703 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308704 (x : int) : (term13 x) = (term15 x).
Proof. exact (@lem2308703 term16 x). Qed.
Lemma lem2308705 (x : int) : (term12 x) = (term15 x).
Proof. exact (TRANS (@lem2308701 x) (@lem2308704 x)). Qed.
Lemma lem2308706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308707 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2308706) (@lem2308705 x)). Qed.
Lemma lem2308708 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem2308709 (x : int) (m : nat) (n : nat) : (term19 x m n) = (term20 x m n).
Proof. exact (MK_COMB (@lem2308707 x) (@lem2308708 m n)). Qed.
Lemma lem2308710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308711 (x : int) (m : nat) (n : nat) : (term21 x m n) = (term22 x m n).
Proof. exact (MK_COMB (@lem2308710) (@lem2308709 x m n)). Qed.
Lemma lem2308713 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308714 (x : int) (m : nat) : (term23 x m) = (term24 x m).
Proof. exact (@lem2308713 x m). Qed.
Lemma lem2308715 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308716 (x : int) (m : nat) : (term25 x m) = (term26 x m).
Proof. exact (MK_COMB (@lem2308715) (@lem2308714 x m)). Qed.
Lemma lem2308718 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308719 (m : nat) (x : int) (n : nat) : (term27 m x n) = (term28 m x n).
Proof. exact (MK_COMB (@lem2308716 x m) (@lem2308718 x n)). Qed.
Lemma lem2308721 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308722 (m : nat) (x : int) (n : nat) : (term28 m x n) = (term29 m x n).
Proof. exact (@lem2308721 (int_pow x m) (int_pow x n)). Qed.
Lemma lem2308723 (m : nat) (x : int) (n : nat) : (term27 m x n) = (term29 m x n).
Proof. exact (TRANS (@lem2308719 m x n) (@lem2308722 m x n)). Qed.
Lemma lem2308724 (m : nat) (x : int) (n : nat) : (term5 m x n) = (term30 m x n).
Proof. exact (MK_COMB (@lem2308711 x m n) (@lem2308723 m x n)). Qed.
Lemma lem2308725 (m : nat) (x : int) (n : nat) : term30 m x n.
Proof. exact (EQ_MP (@lem2308724 m x n) (@lem2308694 m x n)). Qed.
Lemma lem2308726 (m : nat) (n : nat) : term31 m n.
Proof. exact (fun x : int => @lem2308725 m x n). Qed.
Lemma lem2308727 (m : nat) : term32 m.
Proof. exact (fun n : nat => @lem2308726 m n). Qed.
Lemma lem2308728 : term33.
Proof. exact (fun m : nat => @lem2308727 m). Qed.
