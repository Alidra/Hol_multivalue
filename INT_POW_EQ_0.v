Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_0_term_abbrevs.
Require Import REAL_POW_EQ_0_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307836 (x : int) : term0 x.
Proof. exact (@lem1630283 (real_of_int x)). Qed.
Lemma lem2307837 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307838 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2307837 x) (@lem2307836 x)). Qed.
Lemma lem2307839 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2307838 x n). Qed.
Lemma lem2307840 (x : int) (n : nat) : (term2 x n) = (((term3 x n) = term4) = (term5 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2307841 (x : int) (n : nat) : ((term3 x n) = term4) = (term5 x n).
Proof. exact (EQ_MP (@lem2307840 x n) (@lem2307839 x n)). Qed.
Lemma lem2307843 (x : int) (n : nat) : (term3 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307844 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307845 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (MK_COMB (@lem2307844) (@lem2307843 x n)). Qed.
Lemma lem2307847 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307848 : term4 = term10.
Proof. exact (@lem2307847 (NUMERAL 0)). Qed.
Lemma lem2307849 (x : int) (n : nat) : ((term3 x n) = term4) = ((term6 x n) = term10).
Proof. exact (MK_COMB (@lem2307845 x n) (@lem2307848)). Qed.
Lemma lem2307851 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307852 (x : int) (n : nat) : ((term6 x n) = term10) = ((int_pow x n) = term11).
Proof. exact (@lem2307851 (int_pow x n) term11). Qed.
Lemma lem2307853 (x : int) (n : nat) : ((term3 x n) = term4) = ((int_pow x n) = term11).
Proof. exact (TRANS (@lem2307849 x n) (@lem2307852 x n)). Qed.
Lemma lem2307854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307855 (x : int) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (MK_COMB (@lem2307854) (@lem2307853 x n)). Qed.
Lemma lem2307857 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307858 : term4 = term10.
Proof. exact (@lem2307857 (NUMERAL 0)). Qed.
Lemma lem2307859 (x : int) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2307860 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term10).
Proof. exact (MK_COMB (@lem2307859 x) (@lem2307858)). Qed.
Lemma lem2307862 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307863 (x : int) : ((real_of_int x) = term10) = (x = term11).
Proof. exact (@lem2307862 x term11). Qed.
Lemma lem2307864 (x : int) : ((real_of_int x) = term4) = (x = term11).
Proof. exact (TRANS (@lem2307860 x) (@lem2307863 x)). Qed.
Lemma lem2307865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307866 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2307865) (@lem2307864 x)). Qed.
Lemma lem2307867 (n : nat) : (term17 n) = (term17 n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem2307868 (x : int) (n : nat) : (term5 x n) = (term18 x n).
Proof. exact (MK_COMB (@lem2307866 x) (@lem2307867 n)). Qed.
Lemma lem2307869 (x : int) (n : nat) : (((term3 x n) = term4) = (term5 x n)) = (((int_pow x n) = term11) = (term18 x n)).
Proof. exact (MK_COMB (@lem2307855 x n) (@lem2307868 x n)). Qed.
Lemma lem2307870 (x : int) (n : nat) : ((int_pow x n) = term11) = (term18 x n).
Proof. exact (EQ_MP (@lem2307869 x n) (@lem2307841 x n)). Qed.
Lemma lem2307871 (x : int) : term19 x.
Proof. exact (fun n : nat => @lem2307870 x n). Qed.
Lemma lem2307872 : term20.
Proof. exact (fun x : int => @lem2307871 x). Qed.
