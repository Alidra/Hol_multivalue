Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306854_term_abbrevs.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2306824_spec.
Lemma lem2306825 : term0.
Proof. exact (proj2 (@lem2306824)). Qed.
Lemma lem2306826 (x : nat) : term1 x.
Proof. exact (@lem2306825 x). Qed.
Lemma lem2306827 (x : nat) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2306828 (x : nat) : term2 x.
Proof. exact (EQ_MP (@lem2306827 x) (@lem2306826 x)). Qed.
Lemma lem2306829 (x : nat) (n : nat) : term3 x n.
Proof. exact (@lem2306828 x n). Qed.
Lemma lem2306830 (x : nat) (n : nat) : (term3 x n) = ((term4 x n) = (term5 x n)).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem2306831 (x : nat) (n : nat) : (term4 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem2306830 x n) (@lem2306829 x n)). Qed.
Lemma lem2306833 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306834 (x : nat) : (real_of_num x) = (term6 x).
Proof. exact (@lem2306833 x). Qed.
Lemma lem2306835 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2306836 (x : nat) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2306835) (@lem2306834 x)). Qed.
Lemma lem2306837 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2306838 (x : nat) (n : nat) : (term4 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2306836 x) (@lem2306837 n)). Qed.
Lemma lem2306840 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2306841 (x : nat) (n : nat) : (term9 x n) = (term12 x n).
Proof. exact (@lem2306840 (int_of_num x) n). Qed.
Lemma lem2306842 (x : nat) (n : nat) : (term4 x n) = (term12 x n).
Proof. exact (TRANS (@lem2306838 x n) (@lem2306841 x n)). Qed.
Lemma lem2306843 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306844 (x : nat) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (MK_COMB (@lem2306843) (@lem2306842 x n)). Qed.
Lemma lem2306846 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306847 (x : nat) (n : nat) : (term5 x n) = (term15 x n).
Proof. exact (@lem2306846 (Nat.pow x n)). Qed.
Lemma lem2306848 (x : nat) (n : nat) : ((term4 x n) = (term5 x n)) = ((term12 x n) = (term15 x n)).
Proof. exact (MK_COMB (@lem2306844 x n) (@lem2306847 x n)). Qed.
Lemma lem2306850 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306851 (x : nat) (n : nat) : ((term12 x n) = (term15 x n)) = ((term16 x n) = (term17 x n)).
Proof. exact (@lem2306850 (term16 x n) (term17 x n)). Qed.
Lemma lem2306852 (x : nat) (n : nat) : ((term4 x n) = (term5 x n)) = ((term16 x n) = (term17 x n)).
Proof. exact (TRANS (@lem2306848 x n) (@lem2306851 x n)). Qed.
Lemma lem2306853 (x : nat) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem2306852 x n) (@lem2306831 x n)). Qed.
Lemma lem2306854 (x : nat) : term18 x.
Proof. exact (fun n : nat => @lem2306853 x n). Qed.
