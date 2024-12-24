Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_POW_term_abbrevs.
Require Import REAL_SGN_POW_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309919 (x : int) : term0 x.
Proof. exact (@lem1758099 (real_of_int x)). Qed.
Lemma lem2309920 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309921 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309920 x) (@lem2309919 x)). Qed.
Lemma lem2309922 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2309921 x n). Qed.
Lemma lem2309923 (x : int) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2309924 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2309923 x n) (@lem2309922 x n)). Qed.
Lemma lem2309926 (x : int) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2309927 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309928 (x : int) (n : nat) : (term3 x n) = (term7 x n).
Proof. exact (MK_COMB (@lem2309927) (@lem2309926 x n)). Qed.
Lemma lem2309930 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309931 (x : int) (n : nat) : (term7 x n) = (term10 x n).
Proof. exact (@lem2309930 (int_pow x n)). Qed.
Lemma lem2309932 (x : int) (n : nat) : (term3 x n) = (term10 x n).
Proof. exact (TRANS (@lem2309928 x n) (@lem2309931 x n)). Qed.
Lemma lem2309933 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309934 (x : int) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem2309933) (@lem2309932 x n)). Qed.
Lemma lem2309936 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309937 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2309938 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2309937) (@lem2309936 x)). Qed.
Lemma lem2309939 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2309940 (x : int) (n : nat) : (term4 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem2309938 x) (@lem2309939 n)). Qed.
Lemma lem2309942 (x : int) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2309943 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (@lem2309942 (int_sgn x) n). Qed.
Lemma lem2309944 (x : int) (n : nat) : (term4 x n) = (term16 x n).
Proof. exact (TRANS (@lem2309940 x n) (@lem2309943 x n)). Qed.
Lemma lem2309945 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term10 x n) = (term16 x n)).
Proof. exact (MK_COMB (@lem2309934 x n) (@lem2309944 x n)). Qed.
Lemma lem2309947 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309948 (x : int) (n : nat) : ((term10 x n) = (term16 x n)) = ((term17 x n) = (term18 x n)).
Proof. exact (@lem2309947 (term17 x n) (term18 x n)). Qed.
Lemma lem2309949 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term17 x n) = (term18 x n)).
Proof. exact (TRANS (@lem2309945 x n) (@lem2309948 x n)). Qed.
Lemma lem2309950 (x : int) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem2309949 x n) (@lem2309924 x n)). Qed.
Lemma lem2309951 (x : int) : term19 x.
Proof. exact (fun n : nat => @lem2309950 x n). Qed.
Lemma lem2309952 : term20.
Proof. exact (fun x : int => @lem2309951 x). Qed.
