Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_ODD_EQ_term_abbrevs.
Require Import REAL_POW_EQ_ODD_EQ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308088 (n : nat) : term0 n.
Proof. exact (@lem1665320 n). Qed.
Lemma lem2308089 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308090 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308089 n) (@lem2308088 n)). Qed.
Lemma lem2308091 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308090 n (real_of_int x)). Qed.
Lemma lem2308092 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308093 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308092 n x) (@lem2308091 n x)). Qed.
Lemma lem2308094 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308093 n x (real_of_int y)). Qed.
Lemma lem2308095 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308096 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308095 n x y) (@lem2308094 n x y)). Qed.
Lemma lem2308098 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308099 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308100 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308099) (@lem2308098 x n)). Qed.
Lemma lem2308102 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308103 (y : int) (n : nat) : (term6 y n) = (term7 y n).
Proof. exact (@lem2308102 y n). Qed.
Lemma lem2308104 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((term7 x n) = (term7 y n)).
Proof. exact (MK_COMB (@lem2308100 x n) (@lem2308103 y n)). Qed.
Lemma lem2308106 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308107 (x : int) (y : int) (n : nat) : ((term7 x n) = (term7 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (@lem2308106 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308108 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (TRANS (@lem2308104 x y n) (@lem2308107 x y n)). Qed.
Lemma lem2308109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2308110 (x : int) (y : int) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem2308109) (@lem2308108 x y n)). Qed.
Lemma lem2308112 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308113 (n : nat) (x : int) (y : int) : (((term6 x n) = (term6 y n)) = ((real_of_int x) = (real_of_int y))) = (((int_pow x n) = (int_pow y n)) = (x = y)).
Proof. exact (MK_COMB (@lem2308110 x y n) (@lem2308112 x y)). Qed.
Lemma lem2308114 (n : nat) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem2308115 (n : nat) (x : int) (y : int) : (term5 n x y) = (term13 n x y).
Proof. exact (MK_COMB (@lem2308114 n) (@lem2308113 n x y)). Qed.
Lemma lem2308116 (n : nat) (x : int) (y : int) : term13 n x y.
Proof. exact (EQ_MP (@lem2308115 n x y) (@lem2308096 n x y)). Qed.
Lemma lem2308117 (n : nat) (x : int) : term14 n x.
Proof. exact (fun y : int => @lem2308116 n x y). Qed.
Lemma lem2308118 (n : nat) : term15 n.
Proof. exact (fun x : int => @lem2308117 n x). Qed.
Lemma lem2308119 : term16.
Proof. exact (fun n : nat => @lem2308118 n). Qed.
