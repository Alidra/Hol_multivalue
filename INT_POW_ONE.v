Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_ONE_term_abbrevs.
Require Import REAL_POW_ONE_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308851 (n : nat) : term0 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem2308852 (n : nat) : (term0 n) = ((term1 n) = term2).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308853 (n : nat) : (term1 n) = term2.
Proof. exact (EQ_MP (@lem2308852 n) (@lem2308851 n)). Qed.
Lemma lem2308855 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308856 : term2 = term4.
Proof. exact (@lem2308855 term5). Qed.
Lemma lem2308857 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308858 : term6 = term7.
Proof. exact (MK_COMB (@lem2308857) (@lem2308856)). Qed.
Lemma lem2308859 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308860 (n : nat) : (term1 n) = (term8 n).
Proof. exact (MK_COMB (@lem2308858) (@lem2308859 n)). Qed.
Lemma lem2308862 (x : int) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308863 (n : nat) : (term8 n) = (term11 n).
Proof. exact (@lem2308862 term12 n). Qed.
Lemma lem2308864 (n : nat) : (term1 n) = (term11 n).
Proof. exact (TRANS (@lem2308860 n) (@lem2308863 n)). Qed.
Lemma lem2308865 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308866 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem2308865) (@lem2308864 n)). Qed.
Lemma lem2308868 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308869 : term2 = term4.
Proof. exact (@lem2308868 term5). Qed.
Lemma lem2308870 (n : nat) : ((term1 n) = term2) = ((term11 n) = term4).
Proof. exact (MK_COMB (@lem2308866 n) (@lem2308869)). Qed.
Lemma lem2308872 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308873 (n : nat) : ((term11 n) = term4) = ((term15 n) = term12).
Proof. exact (@lem2308872 (term15 n) term12). Qed.
Lemma lem2308874 (n : nat) : ((term1 n) = term2) = ((term15 n) = term12).
Proof. exact (TRANS (@lem2308870 n) (@lem2308873 n)). Qed.
Lemma lem2308875 (n : nat) : (term15 n) = term12.
Proof. exact (EQ_MP (@lem2308874 n) (@lem2308853 n)). Qed.
Lemma lem2308876 : term16.
Proof. exact (fun n : nat => @lem2308875 n). Qed.
