Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EVENPOW_ABS_term_abbrevs.
Require Import REAL_EVENPOW_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301975 (x : int) : term0 x.
Proof. exact (@lem1669140 (real_of_int x)). Qed.
Lemma lem2301976 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301977 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301976 x) (@lem2301975 x)). Qed.
Lemma lem2301978 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2301977 x n). Qed.
Lemma lem2301979 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2301980 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2301979 x n) (@lem2301978 x n)). Qed.
Lemma lem2301982 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301983 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2301984 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2301983) (@lem2301982 x)). Qed.
Lemma lem2301985 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2301986 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2301984 x) (@lem2301985 n)). Qed.
Lemma lem2301988 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2301989 (x : int) (n : nat) : (term9 x n) = (term12 x n).
Proof. exact (@lem2301988 (int_abs x) n). Qed.
Lemma lem2301990 (x : int) (n : nat) : (term8 x n) = (term12 x n).
Proof. exact (TRANS (@lem2301986 x n) (@lem2301989 x n)). Qed.
Lemma lem2301991 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301992 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (MK_COMB (@lem2301991) (@lem2301990 x n)). Qed.
Lemma lem2301994 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2301995 (x : int) (n : nat) : ((term8 x n) = (term10 x n)) = ((term12 x n) = (term11 x n)).
Proof. exact (MK_COMB (@lem2301992 x n) (@lem2301994 x n)). Qed.
Lemma lem2301997 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301998 (x : int) (n : nat) : ((term12 x n) = (term11 x n)) = ((term15 x n) = (int_pow x n)).
Proof. exact (@lem2301997 (term15 x n) (int_pow x n)). Qed.
Lemma lem2301999 (x : int) (n : nat) : ((term8 x n) = (term10 x n)) = ((term15 x n) = (int_pow x n)).
Proof. exact (TRANS (@lem2301995 x n) (@lem2301998 x n)). Qed.
Lemma lem2302000 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2302001 (x : int) (n : nat) : (term3 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem2302000 n) (@lem2301999 x n)). Qed.
Lemma lem2302002 (x : int) (n : nat) : term17 x n.
Proof. exact (EQ_MP (@lem2302001 x n) (@lem2301980 x n)). Qed.
Lemma lem2302003 (x : int) : term18 x.
Proof. exact (fun n : nat => @lem2302002 x n). Qed.
Lemma lem2302004 : term19.
Proof. exact (fun x : int => @lem2302003 x). Qed.
